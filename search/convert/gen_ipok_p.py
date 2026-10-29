#!/usr/bin/env python3
"""gen_ipok_p.py: the E1P version of an earlier gen_ipok.py in --bin mode: the per-IP
data and IPOK fact modules of a <3,3,4> E1P line (up to 255 labels; the point lines h707 / h708 have 255 labels and
417,198 slots), for the point runs.

Usage: gen_ipok_p.py IPFILE TABLE --cls C --ns NS --src NAME --bin --binrel REL [--per 8] [--clstab FILE] [--ipb MODULE]
                     [--recheck 0.01] [--negctl 300] [--seed 334]

  IPFILE   the line's production IP (as read by lineenum9vr); TABLE  table_v2.tsv (c, dim, basis, lb_used: the
           source of B334/Tab2/Data.lean, whose basisOf and lbOf the modules use).
  --cls    the line's class: E = span of its basis column (707 / 708 for the point lines).
  --ns     module directory and namespace (B334.E1x.<NS>; NS may be dotted: Pts.H707). The files tab_<stem>.bin and
           sl_<stem>.bin (stem = NS with '.' -> '_') are written into the working directory;
           --binrel is that directory as seen from the lean directory (e.g. ../data).
  --src    the IP's file name (printed in the log).
  --per    chunks of 512 slots per module S<k> (8: 4096 slots per module; 102 modules for 417,198 slots).
  --clstab the shared B334/E1x/ClsTab.lean: its CL must equal the class table computed from TABLE.
  --ipb    the module with the Boolean IPOK forms (E1P copy of G/IPB.lean), imported by F.lean.
Prints every Lean module between the lines `=== FILE <path under lean/>` and `=== END`, then `=== SUMMARY` lines.
Every printed value is first checked by a Python mirror of the Lean definitions; any failure exits with status 1 and
prints nothing after the failure message.

E1P widths (E1x/CheckP.lean, SlotP.lean, P/Bridge3.lean): label fields of 8 bits (labels 0..254), label planes LB, LBR
and bound fields UB, UBR of 256 bits, slots of 520 bits ([255] label mask, [255] reversed mask, [5] cap, 65 bytes in
sl_*.bin), slot indices of 19 bits, group permutations of 8-bit fields (2048 bits per element). The entries are those of
gen_ipok.py (118 bits, 15 bytes in tab_*.bin; RT9.lean); on an IP with N < 255 the entries are byte-identical to the E1G
generator's.
Dropped from gen_ipok.py: --glob / --cmods (the shared class modules come from the E1G generator, once), --blk / --blkbin
and Fin.lean (the point runs are assembled from many blocks by conv_e1p.py), --single, the inline-table mode.
Added: the class-table cross-check against ClsTab.lean; an independent re-check of a random fraction of the slots from the
written files (own parser, enumerated spans, explicit 3x3 matrices); negative controls (wrong class, wrong witness, both,
wrong cap, wrong label set, wrong group witness); per-slot file slots_<stem>.tsv and group file gorder_<stem>.tsv.

Slots: slot i < nrows is the i-th multi-label row of the file; slot nrows + l is the label bound of label l.
Classes and witnesses (one orbit pass): for each class space K (dim K > dim E) and each tuple of
points of K that some g in G0 sends to E's basis, the spaces h g K (h in the pointwise stabiliser of E's basis) are
superspaces of E of class K with witness h g. Every superspace of E is reached this way; the entry's witness is the
inverse, which maps the row's space onto K.
"""
import argparse
import hashlib
import os
import random
import sys
import time

ID = 273                      # the identity matrix (entry (i, j) at bit 3i + j)
M255 = (1 << 255) - 1
M512 = (1 << 512) - 1
EW = 118                      # entry width (RT9.lean)
EBY = 15                      # bytes per entry in tab_*.bin (#rttablew width 120)
SBY = 65                      # bytes per slot in sl_*.bin (#rttablew width 520)
CW = 96                       # class slot width (RTE.lean)
NL = 255                      # E1P label fields
PW = 256                      # bits per label plane and per bound field
GW = 2048                     # bits per group element: 256 fields of 8 bits
CHUNK = 512                   # entries per literal and per fact
T0 = time.time()


class Fail(Exception):
    pass


def req(c, msg):
    if not c:
        raise Fail(msg)


def log(msg):
    sys.stdout.flush()
    print("# %7.1fs %s" % (time.time() - T0, msg), file=sys.stderr, flush=True)


def par(x):
    return bin(x).count("1") & 1


def mulF(u, v):
    """Act.mulF: the product of 9-bit 3x3 matrices"""
    return ((u & 73) * (v & 7)) ^ (((u >> 1) & 73) * ((v >> 3) & 7)) ^ (((u >> 2) & 73) * ((v >> 6) & 7))


def actF(P, Q, v):
    return mulF(mulF(P, v), Q)


def rref(vecs):
    """the reduced echelon basis (pivot = highest bit) of the span, as a sorted tuple (a canonical key)"""
    piv = {}
    for v in vecs:
        for p, w in piv.items():
            if (v >> p) & 1:
                v ^= w
        if v:
            p = v.bit_length() - 1
            for q in piv:
                if (piv[q] >> p) & 1:
                    piv[q] ^= v
            piv[p] = v
    return tuple(sorted(piv.values()))


def perp(B):
    """a basis of the annihilator of the span of the reduced basis B (pairing <x, y> = par(x & y))"""
    pivots = {v.bit_length() - 1: v for v in B}
    out = []
    for j in range(9):
        if j in pivots:
            continue
        X = 1 << j
        for p, v in pivots.items():
            if (v >> j) & 1:
                X |= 1 << p
        out.append(X)
    return out


def spanmask(vs):
    """RT.spanM: the span by doubling from {0}, as a point mask"""
    S = 1
    for u in vs:
        T = 0
        s = S
        while s:
            b = s & -s
            T |= 1 << ((b.bit_length() - 1) ^ u)
            s ^= b
        S |= T
    return S & M512


BCOL = [sum(1 << w for w in range(512) if (w >> i) & 1) for i in range(9)]


def nperp9(v):
    m = 0
    for i in range(9):
        if (v >> i) & 1:
            m ^= BCOL[i]
    return m


def kermask(duals):
    """RT.kerM9: the common kernel of the functionals, as a point mask"""
    m = M512
    for X in duals:
        m &= M512 ^ nperp9(X)
    return m


def tb(m, i):
    return (m >> i) & 1


# ------------------------------------------------------------------------------------------------ entries and slots
def e_fields(e):
    d = e % 16
    V = [(e >> (4 + 9 * i)) % 512 for i in range(9)]
    return d, V, (e >> 85) % 32, (e >> 90) % 1024, (e >> 100) % 512, (e >> 109) % 512


def lpar(P, X):
    acc = 0
    for i in range(9):
        if (X >> i) & 1:
            acc ^= (P >> (PW * i)) & M255
    return acc


def labM(P, e):
    d, V, _, _, _, _ = e_fields(e)
    acc = M255
    for j in range(9 - d):
        acc &= M255 ^ lpar(P, V[d + j])
    return acc


def slotv(LB, LBR, e):
    """SlotP.slot"""
    return labM(LB, e) | (labM(LBR, e) << 255) | (e_fields(e)[2] << 510)


def dualIn(DOM, e):
    d, V, _, _, _, _ = e_fields(e)
    return all(tb(DOM, V[d + j]) for j in range(9 - d))


class Cls:
    def __init__(self, CL):
        self.CL = CL
        self.dec = {}

    def get(self, c):
        """(n, lb, the n annihilator vectors) of class slot c (the layout of RTE.lean), decoded once"""
        r = self.dec.get(c)
        if r is None:
            n = (self.CL >> (CW * c)) % 16
            r = (n, (self.CL >> (CW * c + 4)) % 32, [(self.CL >> (CW * c + 9 + 9 * j)) % 512 for j in range(n)])
            self.dec[c] = r
        return r

    def n(self, c):
        return self.get(c)[0]

    def lb(self, c):
        return self.get(c)[1]

    def v(self, c, j):
        return self.get(c)[2][j]

    def inK(self, c, w):
        return all(par(w & x) == 0 for x in self.get(c)[2])

    def kM(self, c):
        return kermask(self.get(c)[2])


def entryOK(R, cls, isGL, e):
    """RT.entryOK"""
    d, V, cap, c, P, Q = e_fields(e)
    if d > 9:
        return False
    if spanmask(V[:d]) != kermask(V[d:]):
        return False
    if not (isGL(P) and isGL(Q)):
        return False
    if not all(cls.inK(c, actF(P, Q, V[i])) for i in range(d)):
        return False
    return R <= cap + cls.lb(c)


def classOK(cls, basisOf, lbOf, c):
    """RT.classOK (spanEq through the span mask, which is what inSpan decides for 9-bit vectors)"""
    if cls.lb(c) == 0:
        return True
    return c < 711 and lbOf(c) != 0 and cls.lb(c) <= lbOf(c) and cls.kM(c) == spanmask(basisOf(c))


# ------------------------------------------------------------------------------------------------ inputs
def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def read_classes(path):
    classes = {}
    with open(path) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ci = {h: i for i, h in enumerate(hdr)}
        for line in f:
            t = line.rstrip("\n").split("\t")
            idx, dim = int(t[ci["c"]]), int(t[ci["dim"]])
            bas = [int(x) for x in t[ci["basis"]].split(",")] if t[ci["basis"]] not in ("", "-") else []
            lb = int(t[ci["lb_used"]]) if t[ci["lb_used"]] not in ("", "-") else 0
            req(all(0 < b < 512 for b in bas) and len(rref(bas)) == dim == len(bas), "class %d: basis" % idx)
            req(0 <= lb < 32, "class %d: lb" % idx)
            classes[idx] = (dim, bas, lb)
    req(sorted(classes) == list(range(len(classes))) and len(classes) <= 711, "class ids")
    return classes


class IP:
    def __init__(self, path):
        with open(path) as f:
            t = f.readline().split()
            req(t[0] == "R" and t[2] == "N", "IP line 1")
            self.R, self.N = int(t[1]), int(t[3])
            self.vecs = [int(x) for x in f.readline().split()]
            req(len(self.vecs) == self.N, "IP line 2")
            self.ub = [self.R] * self.N
            self.rows = []                 # multi-label rows: (dim, cap, labels in file order)
            self.G = []
            for line in f:
                t = line.split()
                if not t:
                    continue
                if t[0] == "C":
                    k, c, m = int(t[1]), int(t[2]), int(t[3])
                    ls = [int(x) for x in t[4:4 + m]]
                    req(len(ls) == m and len(t) == 4 + m, "C row length")
                    req(all(0 <= l < self.N for l in ls) and len(set(ls)) == m, "C row labels")
                    if m == 1:
                        self.ub[ls[0]] = min(self.ub[ls[0]], max(0, c))
                        continue
                    req(c >= 0, "negative cap on a multi-label row")
                    self.rows.append((k, c, ls))
                elif t[0] == "G":
                    for _ in range(int(t[1])):
                        self.G.append([int(x) for x in f.readline().split()])
                    break
                else:
                    raise Fail("IP line kind %r" % t[0])
        req(self.N <= NL, "N above 255")
        # the identity first (as conv_e1g.py, whose block literals index this order); gidx: the file index of each element
        self.gidx = list(range(len(self.G)))
        for gi, P in enumerate(self.G):
            if all(P[l] == l for l in range(self.N)):
                self.G[0], self.G[gi] = self.G[gi], self.G[0]
                self.gidx[0], self.gidx[gi] = self.gidx[gi], self.gidx[0]
                break
        req(self.G and all(self.G[0][l] == l for l in range(self.N)), "no identity in G")
        req(all(sorted(P) == list(range(self.N)) for P in self.G), "G: not permutations")
        req(len(set(tuple(P) for P in self.G)) == len(self.G), "G: repeated permutation")
        req(len(self.G) <= 2048, "group above 2048")


# ------------------------------------------------------------------------------------------------ independent re-check
# Nothing below shares code with the generator's main path: 3x3 matrices are lists, spans are enumerated as sets, the
# written tab_/sl_ files are decoded from their bytes, the IP's lines and the class table are parsed again.
def i_mat(v):
    return [[(v >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)]


def i_vec(M):
    return sum(M[i][j] << (3 * i + j) for i in range(3) for j in range(3))


def i_mul(A, B):
    return [[(A[i][0] & B[0][j]) ^ (A[i][1] & B[1][j]) ^ (A[i][2] & B[2][j]) for j in range(3)] for i in range(3)]


def i_inv(P):
    """the inverse of a 9-bit matrix over F2 by the adjugate (checked by the product), None if singular"""
    a = i_mat(P)
    inv = [[(a[(j + 1) % 3][(i + 1) % 3] & a[(j + 2) % 3][(i + 2) % 3]) ^
            (a[(j + 1) % 3][(i + 2) % 3] & a[(j + 2) % 3][(i + 1) % 3]) for j in range(3)] for i in range(3)]
    return i_vec(inv) if i_mul(a, inv) == [[1, 0, 0], [0, 1, 0], [0, 0, 1]] else None


def i_span(gens):
    S = {0}
    for g in gens:
        if g not in S:
            S |= {s ^ g for s in S}
    return S


def i_par(x):
    return sum(1 for ch in bin(x)[2:] if ch == "1") % 2


def i_read_table(path):
    with open(path) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ic, idim, ib, il = hdr.index("c"), hdr.index("dim"), hdr.index("basis"), hdr.index("lb_used")
        T2 = {}
        for line in f:
            t = line.rstrip("\n").split("\t")
            T2[int(t[ic])] = (int(t[idim]), [int(x) for x in t[ib].split(",")] if t[ib] not in ("", "-") else [],
                              int(t[il]) if t[il] not in ("", "-") else 0)
    return T2


def i_valid(R, T2, U, cap, c2, wP2, wQ2):
    """the entry (c2, wP2, wQ2) is valid for the row space U: both matrices invertible, wP2 U wQ2 inside the span of
    class c2's basis, and R <= cap + lb(c2)"""
    if i_inv(wP2) is None or i_inv(wQ2) is None:
        return False
    K2 = i_span(T2[c2][1])
    PM, QM = i_mat(wP2), i_mat(wQ2)
    if not all(i_vec(i_mul(i_mul(PM, i_mat(u)), QM)) in K2 for u in i_span(U)):
        return False
    return R <= cap + T2[c2][2]


def i_recheck(ip_path, table_path, tabfile, slfile, nrows, Ntab, N, R, dimE, basE, sample):
    """re-checks the slots `sample` from the written files; returns {dimension: count}"""
    T2 = i_read_table(table_path)
    with open(tabfile, "rb") as f:
        tabdata = f.read()
    with open(slfile, "rb") as f:
        sldata = f.read()
    req(len(tabdata) == EBY * Ntab and len(sldata) == SBY * Ntab, "recheck: file sizes")
    want_rows = set(i for i in sample if i < nrows)
    got = {}
    with open(ip_path) as f:
        h = f.readline().split()
        req(int(h[1]) == R and int(h[3]) == N, "recheck: IP header")
        vt = [int(x) for x in f.readline().split()]
        ub = [R] * N
        idx = 0
        for line in f:
            if line.isspace():
                continue
            if line[0] == "G":
                break
            t = line.split(None, 4)
            k, cap, m = int(t[1]), int(t[2]), int(t[3])
            if m == 1:
                l = int(t[4])
                ub[l] = min(ub[l], max(0, cap))
            else:
                if idx in want_rows:
                    got[idx] = (k, cap, [int(x) for x in t[4].split()])
                idx += 1
    req(idx == nrows, "recheck: the file has %d multi-label rows, not %d" % (idx, nrows))
    Eset = i_span(basE)
    hi = M255 ^ ((1 << N) - 1)
    lo = (1 << (NL - N)) - 1
    dims = {}
    for i in sorted(sample):
        if i < nrows:
            k, cap, ls = got[i]
        else:
            k, cap, ls = dimE + 1, ub[i - nrows], [i - nrows]
        e = int.from_bytes(tabdata[EBY * i:EBY * (i + 1)], "little")
        bits = format(e, "0%db" % (8 * EBY))[::-1]

        def fld(lo_, w):
            return int(bits[lo_:lo_ + w][::-1], 2)
        d, V = fld(0, 4), [fld(4 + 9 * j, 9) for j in range(9)]
        cap_e, c, wP, wQ = fld(85, 5), fld(90, 10), fld(100, 9), fld(109, 9)
        req(fld(118, 2) == 0, "recheck slot %d: entry top bits" % i)
        U1 = i_span(basE + [vt[l] for l in ls])
        req(len(U1) == 1 << k and d == k and Eset <= U1, "recheck slot %d: row space (dim %d, entry d %d)" % (i, k, d))
        req(i_span(V[:d]) == U1, "recheck slot %d: entry space differs from the row's" % i)
        req(len(i_span(V[d:])) == 1 << (9 - d) and all(i_par(x & u) == 0 for x in V[d:] for u in U1),
            "recheck slot %d: dual vectors" % i)
        req(c in T2 and c < 710 and T2[c][0] == k and T2[c][0] > dimE, "recheck slot %d: class %d" % (i, c))
        K = i_span(T2[c][1])
        req(len(K) == 1 << k, "recheck slot %d: class dim" % i)
        Pi, Qi = i_inv(wP), i_inv(wQ)
        req(Pi is not None and Qi is not None, "recheck slot %d: witness not invertible" % i)
        PM, QM = i_mat(wP), i_mat(wQ)
        req({i_vec(i_mul(i_mul(PM, i_mat(u)), QM)) for u in U1} == K,
            "recheck slot %d: the witness does not map the row space onto class %d" % (i, c))
        PiM, QiM = i_mat(Pi), i_mat(Qi)
        req({i_vec(i_mul(i_mul(PiM, i_mat(x)), QiM)) for x in K} == U1,
            "recheck slot %d: the inverse witness does not map class %d onto the slot space" % (i, c))
        req(cap_e == cap and R <= cap + T2[c][2], "recheck slot %d: cap %d (file %d), class bound %d" % (i, cap_e, cap, T2[c][2]))
        labs = [l for l in range(N) if vt[l] in U1]
        req(sorted(labs) == sorted(ls) and len(labs) == (1 << (k - dimE)) - 1, "recheck slot %d: label set" % i)
        s = int.from_bytes(sldata[SBY * i:SBY * (i + 1)], "little")
        mask = sum(1 << l for l in labs)
        rev = sum(1 << (NL - 1 - l) for l in labs)
        req((s & M255) == (mask | hi) and ((s >> 255) & M255) == (rev | lo) and (s >> 510) == cap,
            "recheck slot %d: sl file value" % i)
        dims[k] = dims.get(k, 0) + 1
    return dims


# ------------------------------------------------------------------------------------------------ Lean text
def hx(n):
    return "0x%x" % n


def fill(text, **kw):
    """the Lean templates use @KEY@ tokens, so Lean's `%` stays literal"""
    for key, val in kw.items():
        text = text.replace("@%s@" % key, str(val))
    return text


def emit(path, text):
    print("=== FILE %s" % path)
    sys.stdout.write(text)
    if not text.endswith("\n"):
        print()
    print("=== END")


T_BASE = """import B334.E1x.@NS@.Data
import B334.E1x.RTE
import B334.E1x.ClsTab
import B334.E1x.IPChk
import B334.Tab2.Data

/-! # The per-slot check of `@NS@` (generated by @GEN@): the slot function agrees with the entry's slot, the entry's
dual vectors lie in the domain, the entry passes `RT.entryOK` against the class table `ClsTab.CL`, and its class is one the
run's hypothesis covers (`c < nCls` and of larger dimension than the run's class @CLS@, as in `RunHyp`,
`Tab2/Induct.lean`). -/

namespace B334.E1x.@NS@

noncomputable def entF (i : Nat) : Bool :=
  SlotP.dualIn DOM (tab i) && RT.entryOK R ClsTab.CL (tab i) && Nat.beq (sl i) (SlotP.slot LB LBR (tab i)) &&
    Nat.blt (RT.eCls (tab i)) Tab2.nCls &&
    Nat.blt (Tab2.basisOf @CLS@).length (Tab2.basisOf (RT.eCls (tab i))).length

end B334.E1x.@NS@
"""

T_F = """import B334.E1x.@NS@.Data
import @IPB@

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Structure facts of `@NS@` (generated by @GEN@; `decide +kernel` on the Boolean forms
of `@IPB@`): the fields of `E1PS.IPOK` other than the slot table, and the group elements `g < NG`. -/

namespace B334.E1x.@NS@
open B334.E1x.E1PS

theorem N_le : N ≤ 255 := by decide
theorem R_le : R ≤ 31 := by decide
theorem R_pos : 1 ≤ R := by decide
theorem DOM_lt : DOM < 2 ^ 512 := by decide +kernel
theorem cosets : Cosets Em VT N := cosets_of (by decide +kernel)
theorem domperp : DomPerp DOM Em := domperp_of (by decide +kernel)
theorem planes : Planes LB VT N := planes_of (by decide +kernel)
theorem planesR : PlanesR LB LBR := planesR_of (by decide +kernel)
theorem Ntab_le : Ntab ≤ 2 ^ 19 := by decide
theorem capslot : ∀ l < N, nrows + l < Ntab ∧ (∀ j < N, (smask (sl (nrows + l))).testBit j = decide (j = l)) ∧
    scap (sl (nrows + l)) = E1P.fld UB l := capslot_of (by decide +kernel)
theorem UB_eq : UB = V (fun l => E1P.fld UB l) := by
  rw [show V (fun l => E1P.fld UB l) = pkL 256 (fun l => E1P.fld UB l) 255 from (pkL_eq _ _ _).symm]; decide +kernel
theorem UBR_eq : UBR = VR (fun l => E1P.fld UB l) := by
  rw [show VR (fun l => E1P.fld UB l) = pkL 256 (fun j => E1P.fld UB (254 - j)) 255 from (pkL_eq _ _ _).symm]
  decide +kernel
theorem UB_le : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32 := uble_of (by decide +kernel)
theorem grpB : IPChk.allR (fun g => geltB Em VT N (GP g) (GE g).1 (GE g).2) 0 NG = true := by decide +kernel
theorem gelt : ∀ g < NG, GElt Em VT N (GP g) (GE g).1 (GE g).2 := fun g hg => gelt_of (IPChk.allR_spec0 grpB g hg)

end B334.E1x.@NS@
"""

T_OK = """@IMPORTS@import B334.E1x.@NS@.F
import B334.E1x.ClsAll

set_option maxRecDepth 100000

/-! # `E1PS.IPOK` and the row bounds of `@NS@` (generated by @GEN@)

`ipokX LF`: every field of `IPOK (Cx LF) Em LB LBR UB UBR Ntab nrows sl tab GE` for any leaf test `LF` (the fields do not
mention it); `ipok` is the instance for `C`. `rows`: the `hrow` of `E1PS.e1_sound`, from the facts of the classes of larger
dimension than the run's class @CLS@ (`hhi`, the hypothesis of `RunHyp`, `Tab2/Induct.lean`) through `RT.rows_of_classes'`.
The slot facts are joined from the per-module range facts `rng_<first slot>` of `S<k>` (@PER@ chunks of 512 slots each). -/

namespace B334.E1x.@NS@
open B334.E1x.E1PS

theorem okAll : IPChk.allR entF 0 Ntab = true := by
@JOINS@
theorem ent_all : ∀ i < Ntab, entF i = true := fun i hi => by
  have h := IPChk.allR_spec entF 0 Ntab okAll i hi
  rwa [Nat.zero_add] at h

theorem sl_spec : ∀ i < Ntab, sl i = SlotP.slot LB LBR (tab i) ∧ SlotP.dualIn DOM (tab i) = true := fun i hi => by
  have h := ent_all i hi
  unfold entF at h
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.2, h.1.1.1.1⟩

theorem sl_zero : ∀ i, Ntab ≤ i → i < 2 ^ 19 → sl i = 0 := fun i h1 _ => by
  unfold sl; exact if_neg (by omega)

theorem grp : ∀ g < 2048, GElt Em VT N (GP g) (GE g).1 (GE g).2 := by
  intro g _
  by_cases h : g < NG
  · exact gelt g h
  · have h0 : (0 : Nat) < NG := by decide
    have e1 : GP g = GP 0 := by unfold GP; rw [if_neg h, if_pos h0]
    have e2 : GE g = GE 0 := by unfold GE; rw [if_neg h, if_pos h0]
    rw [e1, e2]
    exact gelt 0 h0

theorem ipokX (LF : Nat → Bool) : IPOK (Cx LF) Em LB LBR UB UBR Ntab nrows sl tab GE where
  N_le := N_le
  R_le := R_le
  R_pos := R_pos
  DOM_lt := DOM_lt
  cosets := cosets
  domperp := domperp
  planes := planes
  planesR := planesR
  sl_spec := sl_spec
  sl_zero := sl_zero
  Ntab_le := Ntab_le
  UB_eq := UB_eq
  UBR_eq := UBR_eq
  UB_le := UB_le
  capslot := capslot
  grp := grp

theorem ipok : IPOK C Em LB LBR UB UBR Ntab nrows sl tab GE := ipokX LFn

theorem hent : ∀ i < Ntab, RT.entryOK R ClsTab.CL (tab i) = true ∧
    RT.classOK ClsTab.CL Tab2.basisOf Tab2.lbOf (RT.eCls (tab i)) = true ∧
    (RT.eCls (tab i) < Tab2.nCls ∧ (Tab2.basisOf @CLS@).length < (Tab2.basisOf (RT.eCls (tab i))).length) := by
  intro i hi
  have h := ent_all i hi
  unfold entF at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1.2, ClsChk.cls_all _ (by unfold RT.eCls; exact Nat.mod_lt _ (by norm_num)), h.1.2, h.2⟩

/-- the row bounds of the IP from the classes above the run's class -/
theorem rows (hhi : ∀ c', c' < Tab2.nCls → (Tab2.basisOf @CLS@).length < (Tab2.basisOf c').length →
      Tab2.lbOf c' ≠ 0 → RowValid (Tab2.basisOf c') (Tab2.lbOf c')) :
    ∀ i < Ntab, Fact (RT.dualM (tab i)) (R - RT.eCap (tab i)) :=
  RT.rows_of_classes' R ClsTab.CL Ntab tab Tab2.basisOf Tab2.lbOf
    (fun c => c < Tab2.nCls ∧ (Tab2.basisOf @CLS@).length < (Tab2.basisOf c).length)
    (fun c hc => ClsChk.basis_lt c hc.1) (fun c hc _ hlb => hhi c hc.1 hc.2 hlb) hent

end B334.E1x.@NS@
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ip")
    ap.add_argument("table")
    ap.add_argument("--cls", type=int, required=True)
    ap.add_argument("--ns", required=True)
    ap.add_argument("--src", required=True)
    ap.add_argument("--per", type=int, default=8)
    ap.add_argument("--bin", action="store_true")
    ap.add_argument("--binrel", default="")
    ap.add_argument("--clstab", default="")
    ap.add_argument("--ipb", default="B334.E1x.Pts.IPBP")
    ap.add_argument("--recheck", type=float, default=0.01)
    ap.add_argument("--negctl", type=int, default=300)
    ap.add_argument("--seed", type=int, default=334)
    a = ap.parse_args()
    req(a.bin and a.binrel != "", "table mode only: --bin and --binrel are required")
    req(0 < a.recheck <= 1 and a.negctl >= 1 and a.per >= 1, "options")
    marks = [("start", time.time())]

    def mark(name):
        marks.append((name, time.time()))

    ipsha, sdsha = sha(a.ip)[:16], sha(a.table)[:16]
    classes = read_classes(a.table)
    NC = len(classes)
    ip = IP(a.ip)
    R, N = ip.R, ip.N
    req(1 <= R <= 31, "R")
    log("inputs: IP %s (%s) R=%d N=%d rows=%d G=%d; %d classes (%s)" % (a.src, ipsha, R, N, len(ip.rows), len(ip.G),
                                                                         NC, sdsha))
    mark("read inputs")

    # G0
    INV = {}
    for P in range(512):
        for X in range(512):
            if mulF(P, X) == ID:
                INV[P] = X
                break
    GL = sorted(INV)
    req(len(GL) == 168 and all(mulF(INV[P], P) == ID for P in GL), "GL3")

    def isGL(P):
        return P in INV

    # the class table
    CL = 0
    for c in range(NC):
        dim, bas, lb = classes[c]
        duals = perp(rref(bas))
        v = len(duals) | (lb << 4)
        for j, X in enumerate(duals):
            v |= X << (9 + 9 * j)
        CL |= v << (CW * c)
    cls = Cls(CL)

    def basisOf(c):
        return [b % 512 for b in classes[c][1]] if c < NC else []

    def lbOf(c):
        return classes[c][2] if c < NC else 0

    req(all(classOK(cls, basisOf, lbOf, c) for c in range(1024)), "classOK")
    req(all(cls.kM(c) == spanmask(classes[c][1]) for c in range(NC)), "class spaces")
    log("class table: %d classes, classOK for all c < 1024" % NC)
    if a.clstab:
        txt = open(a.clstab).read()
        key = "def CL : Nat := 0x"
        k0 = txt.index(key) + len(key)
        k1 = k0
        while txt[k1] in "0123456789abcdef":
            k1 += 1
        req(int(txt[k0:k1], 16) == CL, "%s: CL differs from the class table computed from %s" % (a.clstab, a.table))
        log("ClsTab.lean: CL equals the class table of %s (sha %s)" % (a.table, sdsha))

    # E, labels, planes, domain
    dimE, basE, _ = classes[a.cls]
    EB = rref(basE)
    Em = spanmask(EB)
    req(N == (1 << (9 - dimE)) - 1, "N vs dim E")
    vt = ip.vecs
    req(all(0 <= v < 512 for v in vt), "representatives")
    VT = sum(v << (9 * l) for l, v in enumerate(vt))
    # Cosets
    req(tb(Em, 0), "cosets.zero")
    Epts = [x for x in range(512) if tb(Em, x)]
    req(all(tb(Em, x ^ y) for x in Epts for y in Epts), "cosets.xor_mem")
    req(all(not tb(Em, vt[l]) for l in range(N)), "cosets.rep_out")
    req(all(not tb(Em, vt[l] ^ vt[k]) for l in range(N) for k in range(N) if l != k), "cosets.rep_dist")
    req(all(tb(Em, x) or any(tb(Em, x ^ vt[l]) for l in range(N)) for x in range(512)), "cosets.cover")
    DOM = 0
    for X in range(1, 512):
        if all(par(X & e) == 0 for e in EB):
            DOM |= 1 << X
    req(all(par(e & X) == 0 for X in range(512) if tb(DOM, X) for e in Epts), "domperp")
    LB = 0
    for i in range(9):
        for l in range(N):
            if (vt[l] >> i) & 1:
                LB |= 1 << (PW * i + l)
    LBR = 0
    for i in range(9):
        for j in range(NL):
            if tb(LB, PW * i + (NL - 1) - j):
                LBR |= 1 << (PW * i + j)
    req(all(tb(LB, PW * i + l) == ((l < N) and (vt[l] >> i) & 1) for i in range(9) for l in range(NL)), "planes")
    req(all(tb(LBR, PW * i + j) == tb(LB, PW * i + (NL - 1) - j) for i in range(9) for j in range(NL)), "planesR")
    req(all(u <= R for u in ip.ub), "label bounds")
    UB = sum(ip.ub[l] << (PW * l) for l in range(N))
    UBR = sum(ip.ub[l] << (PW * (NL - 1 - l)) for l in range(N))
    lbE = classes[a.cls][2]
    log("E: class %d dim %d, lb_used %d (R + 1 = %d); %d labels, DOM %d functionals" % (
        a.cls, dimE, lbE, R + 1, N, bin(DOM).count("1")))
    mark("class table, planes")

    # orbit pass: every superspace of E with its class and a witness g (g K_c = U)
    fib = {}
    for P in GL:
        for Q in GL:
            key = tuple(actF(INV[P], INV[Q], e) for e in EB)
            fib.setdefault(key, []).append((P, Q))
    H0 = fib[tuple(EB)]
    # tuples of points of K that are g^-1 of E's basis for some g, walked down the prefix tree of the fibre keys
    nxt = {}
    for key in fib:
        for i in range(len(key)):
            nxt.setdefault(key[:i], set()).add(key[i])
    found = {}
    npairs = 0
    for c in range(NC):
        dim, bas, _ = classes[c]
        if dim <= dimE:
            continue
        KB = rref(bas)
        Km = spanmask(KB)
        stack = [()]
        tuples = []
        while stack:
            t = stack.pop()
            if len(t) == len(EB):
                tuples.append(t)
                continue
            for x in nxt.get(t, ()):
                if tb(Km, x):
                    stack.append(t + (x,))
        for t in tuples:
            npairs += 1
            P0, Q0 = fib[t][0]
            U0 = rref([actF(P0, Q0, b) for b in KB])
            if U0 in found:
                req(found[U0][0] == c, "two classes share an orbit: %d, %d" % (found[U0][0], c))
                continue
            for Ph, Qh in H0:
                U = rref([actF(Ph, Qh, u) for u in U0])
                if U not in found:
                    found[U] = (c, (mulF(Ph, P0), mulF(Q0, Qh)))
    want = 0
    for k in range(1, 10 - dimE):
        num = den = 1
        for i in range(k):
            num *= (1 << (9 - dimE - i)) - 1
            den *= (1 << (k - i)) - 1
        want += num // den
    req(len(found) == want, "orbit pass: %d superspaces, expected %d" % (len(found), want))
    log("orbit pass: %d superspaces of E (dim %d), %d point tuples, |H0| = %d" % (len(found), dimE, npairs, len(H0)))
    mark("orbit pass")

    # entries
    rowsets = [(k, c, ls, "row") for (k, c, ls) in ip.rows] + \
              [(dimE + 1, ip.ub[l], [l], "lab") for l in range(N)]
    nrows, Ntab = len(ip.rows), len(rowsets)
    req(Ntab <= 1 << 19, "slots above 2^19")
    vbit = [1 << v for v in vt]
    # labels >= N lie in every row (their planes are 0), as in conv_e1g.py's slot_value
    hi = M255 ^ ((1 << N) - 1)
    lo = (1 << (NL - N)) - 1

    def slot_status(k, cap, ls, U, Um, c, wP, wQ):
        """the per-slot checks of gen_ipok.py for the entry (c, wP, wQ) of the row space U (the rref tuple, point mask
        Um, label list ls): (status, entry, slot value); status is 'ok' or the first failing check"""
        if classes[c][0] != k:
            return "class dim", 0, 0
        V = list(U) + perp(U)
        e = k
        for j, v in enumerate(V):
            e |= v << (4 + 9 * j)
        e |= (cap << 85) | (c << 90) | (wP << 100) | (wQ << 109)
        if not (len(V) == 9 and cap < 32 and e < 1 << EW):
            return "fields", e, 0
        if not entryOK(R, cls, isGL, e):
            return "entryOK", e, 0
        if not dualIn(DOM, e):
            return "dualIn", e, 0
        # the run's hypothesis covers the slot's class: c < nCls and dim c > dim E (RunHyp, Tab2/Induct.lean)
        if not (c < NC and len(classes[c][1]) > len(basE)):
            return "class not above E", e, 0
        mask = 0
        rev = 0
        for l in ls:
            mask |= 1 << l
            rev |= 1 << (NL - 1 - l)
        inU = 0
        for l in range(N):
            if Um & vbit[l]:
                inU |= 1 << l
        if inU != mask:
            return "label set", e, 0
        sv = slotv(LB, LBR, e)
        if sv != (mask | hi) | ((rev | lo) << 255) | (cap << 510):
            return "slot value", e, sv
        return "ok", e, sv

    tab = []
    slots_v = []
    used = {}
    slack = {}
    bad = []
    stem = a.ns.replace(".", "_")
    nspath = a.ns.replace(".", "/")
    tsv = open("slots_%s.tsv" % stem, "w")
    tsv.write("slot\tkind\tdim\tcap\tnlab\tclass\twP\twQ\n")
    for i, (k, cap, ls, kind) in enumerate(rowsets):
        U = rref(list(EB) + [vt[l] for l in ls])
        req(len(U) == k, "slot %d: dim %d, file says %d" % (i, len(U), k))
        c, (P, Q) = found[U]
        wP, wQ = INV[P], INV[Q]
        st, e, sv = slot_status(k, cap, ls, U, spanmask(U), c, wP, wQ)
        s = cap + classes[c][2] - R
        slack[s] = slack.get(s, 0) + 1
        if st != "ok":
            bad.append((i, kind, k, cap, c, classes[c][2], st))
            continue
        used[c] = used.get(c, 0) + 1
        tab.append(e)
        slots_v.append(sv)
        tsv.write("%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\n" % (i, kind, k, cap, len(ls), c, wP, wQ))
    tsv.close()
    if bad:
        for b in bad[:20]:
            print("BAD slot %d (%s): dim %d cap %d class %d lb %d: %s" % b)
        raise Fail("%d slots fail the slot checks (first 20 above)" % len(bad))
    for l in range(N):
        sv = slots_v[nrows + l]
        req((sv % (1 << 255)) % (1 << N) == 1 << l and (sv >> 510) % 32 == ip.ub[l], "capslot %d" % l)
    log("entries: %d slots (%d rows + %d label bounds), %d classes used, slack %s" % (
        Ntab, nrows, N, len(used), " ".join("%d:%d" % kv for kv in sorted(slack.items()))))
    mark("entries")

    # group witnesses
    stabE = [(P, Q) for P in GL for Q in GL if all(tb(Em, actF(P, Q, e)) for e in EB)]

    def gwit_ok(P, Q, pi):
        """GElt: (P, Q) is in GL x GL, fixes E, and induces the label permutation pi"""
        return (isGL(P) and isGL(Q) and all(tb(Em, actF(P, Q, x)) == tb(Em, x) for x in range(512)) and
                all(pi[l] < N and tb(Em, actF(P, Q, vt[l]) ^ vt[pi[l]]) for l in range(N)))

    GE = []
    for gi, pi in enumerate(ip.G):
        w = None
        for P, Q in stabE:
            if all(tb(Em, actF(P, Q, vt[l]) ^ vt[pi[l]]) for l in range(N)):
                w = (P, Q)
                break
        req(w is not None, "group element %d: no witness in Stab(E)" % gi)
        req(gwit_ok(w[0], w[1], pi), "group element %d: witness check" % gi)
        GE.append(w)
    NG = len(ip.G)
    GPT = 0
    GET = 0
    for g, pi in enumerate(ip.G):
        GPT |= sum(pi[l] << (8 * l) for l in range(N)) << (GW * g)
        GET |= (GE[g][0] | (GE[g][1] << 9)) << (18 * g)
    with open("gorder_%s.tsv" % stem, "w") as f:
        f.write("g\tfile_index\tP\tQ\n")
        for g in range(NG):
            f.write("%d\t%d\t%d\t%d\n" % (g, ip.gidx[g], GE[g][0], GE[g][1]))
    log("group: %d permutations, |Stab(E)| = %d, all witnessed" % (NG, len(stabE)))
    mark("group witnesses")

    # the tables as binary files in the run directory, loaded by #rttablew (B334/E1x/Load.lean)
    tabdata = b"".join(e.to_bytes(EBY, "little") for e in tab)
    sldata = b"".join(s.to_bytes(SBY, "little") for s in slots_v)
    binsha = {}
    for nm, data in (("tab", tabdata), ("sl", sldata)):
        with open("%s_%s.bin" % (nm, stem), "wb") as f:
            f.write(data)
        binsha[nm] = hashlib.sha256(data).hexdigest()
    log("tables: tab_%s.bin (%s), sl_%s.bin (%s) in %s" % (stem, binsha["tab"][:16], stem, binsha["sl"][:16], os.getcwd()))
    mark("tables")

    # independent re-check of a random fraction of the slots, from the written files
    rnd = random.Random(a.seed)
    sample = set(rnd.sample(range(Ntab), max(1, int(round(a.recheck * Ntab)))))
    sample |= {0, nrows - 1, nrows, Ntab - 1}
    firstdim = {}
    for i, (k, _, _) in enumerate(ip.rows):
        firstdim.setdefault(k, i)
    sample |= set(firstdim.values())
    dims = i_recheck(a.ip, a.table, "tab_%s.bin" % stem, "sl_%s.bin" % stem, nrows, Ntab, N, R, dimE, list(basE), sample)
    log("independent re-check: %d slots (%.2f%%) from the written files, by dimension %s: all OK" % (
        len(sample), 100.0 * len(sample) / Ntab, " ".join("%d:%d" % kv for kv in sorted(dims.items()))))
    mark("independent re-check")

    # negative controls: each mutant must be rejected by the generator's checks exactly when the independent evaluation
    # says it is invalid, and every mutant below is invalid by construction (or by that evaluation)
    T2 = i_read_table(a.table)
    bydim = {}
    for cid, (dm, _, _) in classes.items():
        bydim.setdefault(dm, []).append(cid)
    rn = random.Random(a.seed + 1)
    ctl = {}
    for i in rn.sample(range(Ntab), min(Ntab, a.negctl)):
        d, V, cap, c, wP, wQ = e_fields(tab[i])
        U = tuple(V[:d])
        Um = spanmask(U)
        ls = rowsets[i][2]
        k = d
        # the unmutated slot passes, so every rejection below is due to the mutation
        req(Um == spanmask(list(EB) + [vt[l] for l in ls]), "control base slot %d: space" % i)
        st, _, _ = slot_status(k, cap, ls, U, Um, c, wP, wQ)
        req(st == "ok", "control base slot %d: %s" % (i, st))
        alts = [x for x in bydim[k] if x != c]
        for kind in ("class", "witness", "both"):
            if kind != "witness" and not alts:
                continue
            cc = rn.choice(alts) if kind != "witness" else c
            for _ in range(200):
                P2, Q2 = (INV[rn.choice(GL)], INV[rn.choice(GL)]) if kind != "class" else (wP, wQ)
                if not i_valid(R, T2, U, cap, cc, P2, Q2):
                    break
            else:
                raise Fail("control %s on slot %d: no invalid mutant found" % (kind, i))
            st, _, _ = slot_status(k, cap, ls, U, Um, cc, P2, Q2)
            req(st == "entryOK", "control %s on slot %d: the mutant was not rejected by entryOK (%s)" % (kind, i, st))
            ctl[kind] = ctl.get(kind, 0) + 1
        cap2 = R - classes[c][2] - 1
        if cap2 >= 0:
            st, _, _ = slot_status(k, cap2, ls, U, Um, c, wP, wQ)
            req(st == "entryOK" and not i_valid(R, T2, U, cap2, c, wP, wQ), "control cap on slot %d: %s" % (i, st))
            ctl["cap"] = ctl.get("cap", 0) + 1
        if len(ls) >= 2:
            st, _, _ = slot_status(k, cap, ls[:-1], U, Um, c, wP, wQ)
            req(st == "label set", "control label drop on slot %d: %s" % (i, st))
            ctl["label drop"] = ctl.get("label drop", 0) + 1
        sls = set(ls)
        extra = [l for l in range(N) if l not in sls]
        if extra:
            st, _, _ = slot_status(k, cap, ls + [rn.choice(extra)], U, Um, c, wP, wQ)
            req(st == "label set", "control label add on slot %d: %s" % (i, st))
            ctl["label add"] = ctl.get("label add", 0) + 1
    for g in range(min(NG, 60)):
        h = (g * 7 + 3) % NG
        if ip.G[h] != ip.G[g]:
            req(not gwit_ok(GE[g][0], GE[g][1], ip.G[h]), "control group: witness %d accepted for element %d" % (g, h))
            ctl["group witness"] = ctl.get("group witness", 0) + 1
    req(all(kd in ctl for kd in ("class", "witness", "both", "cap", "label drop", "label add", "group witness")),
        "negative controls: a kind was never exercised: %s" % sorted(ctl))
    log("negative controls (every mutant rejected): %s" % ", ".join("%s %d" % kv for kv in sorted(ctl.items())))
    mark("negative controls")

    # ---------------------------------------------------------------------------------------- Lean modules
    NS = a.ns
    gen = "a script"
    nch = (Ntab + CHUNK - 1) // CHUNK
    o = []
    o.append("import B334.E1x.SlotP\nimport B334.E1x.Load\n\n")
    o.append("/-! # E1P data of the IP of class %d (R = %d), generated by %s\n\n" % (a.cls, R, gen))
    o.append("`E` is the span of the class basis `%s`.\n" % ",".join(map(str, basE)))
    o.append("* `VT`: the label representatives (9-bit fields); `LB`, `LBR`: the label planes (plane `i` = bit `i` of "
             "every\n  representative, 256 bits per plane; `LBR` reversed); `DOM`: the nonzero functionals vanishing "
             "on `E`; `Em`: `E`.\n")
    o.append("* `UB`, `UBR`: the label bounds (256-bit fields; `UBR` reversed).\n")
    o.append("* `GP g`: the IP's %d label permutations (8-bit fields, 2048 bits per element; the identity first), padded "
             "with element 0 to 2048;\n  `GE g`: a witness `(P, Q)` in G₀ inducing `GP g`.\n" % NG)
    o.append("* `tab i`: the row-table entry of slot `i` (layout of `RT9.lean`): slot `i < nrows` is the `i`-th "
             "multi-label row\n  of the file, slot `nrows + l` the label bound of `l`. `sl` is the slot function of "
             "the replay.\n")
    o.append("* Both are loaded from binary data files (`#rttablew`, chunks of 512):"
             "\n  `tab_%s.bin` (15-byte entries, sha256 %s) and `sl_%s.bin` (65-byte slots, sha256 %s); the facts"
             "\n  check `sl i = SlotP.slot LB LBR (tab i)` for every slot. -/\n\n" % (
                 stem, binsha["tab"][:16], stem, binsha["sl"][:16]))
    o.append("#rttablew B334.E1x.%s.TBT \"%s/tab_%s.bin\" 512 120\n" % (NS, a.binrel, stem))
    o.append("#rttablew B334.E1x.%s.SLT \"%s/sl_%s.bin\" 512 520\n\n" % (NS, a.binrel, stem))
    o.append("namespace B334.E1x.%s\n\nnoncomputable section\n\n" % NS)
    o.append("def R : Nat := %d\ndef N : Nat := %d\n" % (R, N))
    for nm, v in (("VT", VT), ("Em", Em), ("DOM", DOM), ("LB", LB), ("LBR", LBR), ("UB", UB), ("UBR", UBR)):
        o.append("def %s : Nat := %s\n" % (nm, hx(v)))
    o.append("def NG : Nat := %d\n" % NG)
    o.append("def GPT : Nat := %s\n" % hx(GPT))
    o.append("def GET : Nat := %s\n" % hx(GET))
    o.append("def GP (g : Nat) : Nat := (GPT >>> (2048 * (if g < NG then g else 0))) % 2 ^ 2048\n")
    o.append("def GE (g : Nat) : Nat × Nat :=\n  ((GET >>> (18 * (if g < NG then g else 0))) % 512, "
             "(GET >>> (18 * (if g < NG then g else 0) + 9)) % 512)\n")
    o.append("def Ntab : Nat := %d\ndef nrows : Nat := %d\n\n" % (Ntab, nrows))
    o.append("def tab (i : Nat) : Nat := TBT.entry i\n")
    o.append("def sl (i : Nat) : Nat := if i < Ntab then SLT.entry i else 0\n")
    o.append("def LFn (_pl : Nat) : Bool := false\n")
    o.append("/-- the context of the checker for the leaf test `LF` (at assembly: membership in the run's leaf list) -/\n")
    o.append("def Cx (LF : Nat → Bool) : E1P.Ctx := { R := R, N := N, VT := VT, DOM := DOM, GP := GP, LF := LF }\n")
    o.append("def C : E1P.Ctx := Cx LFn\n\n")
    o.append("end\n\nend B334.E1x.%s\n" % NS)
    emit("B334/E1x/%s/Data.lean" % nspath, "".join(o))

    emit("B334/E1x/%s/Base.lean" % nspath, fill(T_BASE, NS=NS, GEN=gen, CLS=a.cls))

    starts = list(range(0, Ntab, CHUNK))
    mods = []
    rngs = []
    for mi in range(0, len(starts), a.per):
        grp = starts[mi:mi + a.per]
        nm = "S%d" % (mi // a.per)
        mods.append(nm)
        lens = [min(CHUNK, Ntab - s0) for s0 in grp]
        rngs.append((grp[0], sum(lens)))
        t = ["import B334.E1x.%s.Base\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n" % NS,
             "/-! # Entry checks of `%s`, slots %d … %d (generated by %s; `decide +kernel`) -/\n\n" % (
                 NS, grp[0], grp[0] + sum(lens) - 1, gen),
             "namespace B334.E1x.%s\n\n" % NS]
        for s0, m in zip(grp, lens):
            t.append("theorem ok_%d : IPChk.allR entF %d %d = true := by decide +kernel\n" % (s0, s0, m))
        if len(grp) == 1:
            t.append("\ntheorem rng_%d : IPChk.allR entF %d %d = true := ok_%d\n" % (grp[0], grp[0], lens[0], grp[0]))
        else:
            t.append("\n/-- the module's slots joined: `IPChk.allR entF %d %d` -/\n" % (grp[0], sum(lens)))
            t.append("theorem rng_%d : IPChk.allR entF %d %d = true := by\n" % (grp[0], grp[0], sum(lens)))
            acc = lens[0]
            t.append("  have h0 : IPChk.allR entF %d %d = true := ok_%d\n" % (grp[0], acc, grp[0]))
            for q in range(1, len(grp)):
                t.append("  have h%d : IPChk.allR entF %d %d = true := IPChk.allR_join entF %d %d %d h%d ok_%d\n" % (
                    q, grp[0], acc + lens[q], grp[0], acc, lens[q], q - 1, grp[q]))
                acc += lens[q]
            t.append("  exact h%d\n" % (len(grp) - 1))
        t.append("\nend B334.E1x.%s\n" % NS)
        emit("B334/E1x/%s/%s.lean" % (nspath, nm), "".join(t))

    emit("B334/E1x/%s/F.lean" % nspath, fill(T_F, NS=NS, GEN=gen, IPB=a.ipb))

    joins = ["  have h0 : IPChk.allR entF 0 %d = true := rng_%d\n" % (rngs[0][1], rngs[0][0])]
    acc = rngs[0][1]
    for q in range(1, len(rngs)):
        s0, m = rngs[q]
        joins.append("  have h%d : IPChk.allR entF 0 %d = true := IPChk.allR_join entF 0 %d %d h%d rng_%d\n" % (
            q, acc + m, acc, m, q - 1, s0))
        acc += m
    joins.append("  exact h%d\n" % (len(rngs) - 1))
    req(acc == Ntab, "range joins cover %d slots, not %d" % (acc, Ntab))
    emit("B334/E1x/%s/OK.lean" % nspath, fill(T_OK, NS=NS, GEN=gen, CLS=a.cls, PER=a.per, JOINS="".join(joins),
                                              IMPORTS="".join("import B334.E1x.%s.%s\n" % (NS, m) for m in mods)))
    mark("lean text")

    print("=== SUMMARY")
    print("ip %s sha %s table sha %s class %d R %d N %d dimE %d lb_used(E) %d" % (a.src, ipsha, sdsha, a.cls, R, N, dimE, lbE))
    print("slots %d rows %d labels %d chunks %d modules %d (%s..%s) per module <= %d slots" % (
        Ntab, nrows, N, nch, len(mods), mods[0], mods[-1], a.per * CHUNK))
    print("classes used %d: %s" % (len(used), " ".join("%d:%d" % kv for kv in sorted(used.items()))))
    print("slack (cap + lb - R): %s" % " ".join("%d:%d" % kv for kv in sorted(slack.items())))
    print("group %d stabE %d identity was file element %d" % (NG, len(stabE), ip.gidx[0]))
    print("tab sha256 %s" % binsha["tab"])
    print("sl sha256 %s" % binsha["sl"])
    print("independent re-check: %d slots, by dimension %s" % (len(sample), " ".join("%d:%d" % kv for kv in sorted(dims.items()))))
    print("negative controls (mutants, every one rejected): %s" % ", ".join("%s %d" % kv for kv in sorted(ctl.items())))
    print("timing: %s; total %.1fs" % (", ".join("%s %.1fs" % (marks[j][0], marks[j][1] - marks[j - 1][1])
                                                  for j in range(1, len(marks))), time.time() - T0))
    log("done")


if __name__ == "__main__":
    try:
        main()
    except Fail as ex:
        print("FAIL: %s" % ex)
        sys.exit(1)
