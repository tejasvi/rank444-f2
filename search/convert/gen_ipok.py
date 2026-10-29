#!/usr/bin/env python3
"""gen_ipok.py: the per-IP data and IPOK fact modules of a <3,3,4> E1G line, and the shared class modules.

Usage: gen_ipok.py IPFILE TABLE --cls C --ns NS --src NAME [--glob] [--per 8] [--cmods 8] [--blk MOD.CONST]

  IPFILE   the line's production IP (as read by lineenum9vr); TABLE  table_v2.tsv (c, dim, basis, lb_used: the
           source of B334/Tab2/Data.lean, whose basisOf and lbOf the modules use).
  --cls    the line's class: E = span of its basis column.   --ns  module directory and namespace (B334.E1x.<NS>).
  --src    the IP's file name (printed in the log).
  --glob   also print the shared class modules: ClsTab (the class table CL, bound = lb_used), ClsBase, ClsOK<k>,
           ClsAll.
  --blk    the block literal of the run (one block, no glue, no leaves: converter v0), e.g. Rep692b.S in module
           B334.E1x.Rep692b; prints the run theorem module Fin.lean.
Prints every Lean module between the lines `=== FILE <path under lean/>` and `=== END`, then `=== SUMMARY` lines.
Every printed value is first checked by a Python mirror of the Lean definitions; any failure exits with status 1 and
prints nothing after the failure message.

Slots: slot i < nrows is the i-th multi-label row of the file; slot nrows + l is the label bound of label l.
Classes and witnesses (one orbit pass): for each class space K (dim K > dim E) and each tuple of
points of K that some g in G0 sends to E's basis, the spaces h g K (h in the pointwise stabiliser of E's basis) are
superspaces of E of class K with witness h g. Every superspace of E is reached this way; the entry's witness is the
inverse, which maps the row's space onto K.
"""
import argparse
import hashlib
import os
import sys
import time

ID = 273                      # the identity matrix (entry (i, j) at bit 3i + j)
M127 = (1 << 127) - 1
M512 = (1 << 512) - 1
EW = 118                      # entry width (RT9.lean)
CW = 96                       # class slot width (RTE.lean)
NL = 127                      # E1G label fields
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
            acc ^= (P >> (128 * i)) & M127
    return acc


def labM(P, e):
    d, V, _, _, _, _ = e_fields(e)
    acc = M127
    for j in range(9 - d):
        acc &= M127 ^ lpar(P, V[d + j])
    return acc


def slotv(LB, LBR, e):
    """SlotG.slot"""
    return labM(LB, e) | (labM(LBR, e) << 127) | (e_fields(e)[2] << 254)


def dualIn(DOM, e):
    d, V, _, _, _, _ = e_fields(e)
    return all(tb(DOM, V[d + j]) for j in range(9 - d))


class Cls:
    def __init__(self, CL):
        self.CL = CL

    def n(self, c):
        return (self.CL >> (CW * c)) % 16

    def lb(self, c):
        return (self.CL >> (CW * c + 4)) % 32

    def v(self, c, j):
        return (self.CL >> (CW * c + 9 + 9 * j)) % 512

    def inK(self, c, w):
        return all(par(w & self.v(c, j)) == 0 for j in range(self.n(c)))

    def kM(self, c):
        return kermask([self.v(c, j) for j in range(self.n(c))])


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
        req(self.N <= NL, "N above 127")
        # the identity first (as conv_e1g.py, whose block literals index this order)
        for gi, P in enumerate(self.G):
            if all(P[l] == l for l in range(self.N)):
                self.G[0], self.G[gi] = self.G[gi], self.G[0]
                break
        req(self.G and all(self.G[0][l] == l for l in range(self.N)), "no identity in G")
        req(all(sorted(P) == list(range(self.N)) for P in self.G), "G: not permutations")
        req(len(set(tuple(P) for P in self.G)) == len(self.G), "G: repeated permutation")
        req(len(self.G) <= 2048, "group above 2048")


# ------------------------------------------------------------------------------------------------ Lean text
def hx(n):
    return "0x%x" % n


def tree(lo, hi, name):
    if hi - lo == 1:
        return "%s%d" % (name, lo)
    mid = (lo + hi) // 2
    return "cond (Nat.blt k %d) (%s) (%s)" % (mid, tree(lo, mid, name), tree(mid, hi, name))


def emit(path, text):
    print("=== FILE %s" % path)
    sys.stdout.write(text)
    if not text.endswith("\n"):
        print()
    print("=== END")


LFCH = 100   # leaves per leaf-check module (about 900 leaves checked in one Fin module took 15 GB)


def leaf_modules(out, NS, gen, cls, LI):
    """the leaf-check modules (LfB: the per-leaf check; Lf<k>: LFCH leaves each) and the Fin text of hLF"""
    if not LI:
        return "", "(fun _ h => by simp [C, LFn] at h)"
    out("B334/E1x/%s/LfB.lean" % NS, """import B334.E1x.%(NS)s.Data
import B334.E1x.G.Bridge2
import B334.T2.Index
import B334.BCP.PermL
import B334.E1x.IPChk

/-! # The per-leaf check of `%(NS)s` (generated by %(gen)s): leaf `q = (pl, i)` is covered by record `i` of
`T2.leaves_%(c)d` with the identity permutation -/

namespace B334.E1x.%(NS)s
open B334.E1x.E1GS

noncomputable def leafB (q : Nat × Nat) : Bool :=
  Nat.blt q.2 T2.leaves_%(c)d.length &&
    B334.BCP.t2match (T2.leaves_%(c)d.getD q.2 0) (termsOf R VT q.1) R DOM (List.range R)

end B334.E1x.%(NS)s
""" % {"NS": NS, "gen": gen, "c": cls})
    n = len(LI)
    rngs = [(lo, min(n, lo + LFCH)) for lo in range(0, n, LFCH)]
    for q, (lo, hi) in enumerate(rngs):
        out("B334/E1x/%s/Lf%d.lean" % (NS, q), "import B334.E1x.%s.LfB\n\nset_option maxHeartbeats 0\n"
            "set_option maxRecDepth 100000\n\n/-! # Leaves %d … %d of `%s` (generated by %s; `decide +kernel`) -/\n\n"
            "namespace B334.E1x.%s\n\ntheorem lf_%d : IPChk.allR (fun k => leafB (LI.getD k (0, 0))) %d %d = true := by\n"
            "  decide +kernel\n\nend B334.E1x.%s\n" % (NS, lo, hi - 1, NS, gen, NS, lo, lo, hi - lo, NS))
    f = "(fun k => leafB (LI.getD k (0, 0)))"
    jl = ["  have h0 : IPChk.allR %s 0 %d = true := lf_0\n" % (f, rngs[0][1])]
    for q in range(1, len(rngs)):
        lo, hi = rngs[q]
        jl.append("  have h%d : IPChk.allR %s 0 %d = true := IPChk.allR_join %s 0 %d %d h%d lf_%d\n" % (
            q, f, hi, f, lo, hi - lo, q - 1, lo))
    jl.append("  exact h%d\n" % (len(rngs) - 1))
    thm = ("theorem leafAll : IPChk.allR %s 0 %d = true := by\n" % (f, n) + "".join(jl) + "\n"
           "theorem hLF : ∀ pl, C.LF pl = true → B334.BCP.NoDecomp (termsOf C.R C.VT pl) C.R C.DOM := by\n"
           "  intro pl h\n"
           "  change LI.any (fun q => Nat.beq q.1 pl) = true at h\n"
           "  obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp h\n"
           "  obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.mp hq\n"
           "  have hlen : LI.length = %d := by decide\n" % n +
           "  have hc : leafB (LI.getD k (0, 0)) = true := IPChk.allR_spec0 leafAll k (by rw [← hlen]; exact hk)\n"
           "  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hkq] at hc\n"
           "  unfold leafB at hc\n"
           "  simp only [Bool.and_eq_true, Nat.blt_eq] at hc\n"
           "  have hm : T2.leaves_%d.getD q.2 0 ∈ T2.leaves_%d := by\n" % (cls, cls) +
           "    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc.1, Option.getD_some]\n"
           "    exact List.getElem_mem hc.1\n"
           "  rw [← Nat.eq_of_beq_eq_true hqe]\n"
           "  exact B334.BCP.noDecomp_of_t2 (List.range R) hc.2 (T2.ok_%d _ hm)\n\n" % cls)
    return thm, "hLF"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ip")
    ap.add_argument("table")
    ap.add_argument("--cls", type=int, required=True)
    ap.add_argument("--ns", required=True)
    ap.add_argument("--src", required=True)
    ap.add_argument("--glob", action="store_true")
    ap.add_argument("--per", type=int, default=8)
    ap.add_argument("--cmods", type=int, default=8)
    ap.add_argument("--blk", default="")
    ap.add_argument("--bin", action="store_true")
    ap.add_argument("--binrel", default="")
    ap.add_argument("--blkbin", default="", help="the block literal file (#e1lits, written by conv_e1g.py --bin) in "
                    "the run directory; the run theorem replays its literal BLK.L0")
    ap.add_argument("--single", action="store_true", help="print all modules of the IP as one module NS/All.lean")
    ap.add_argument("--blkinfo", default="", help="the info file of conv_e1g_v1.py single (pieces, glue witnesses W, "
                    "leaves): the run is the list of pieces BLK.lits; prints block-check modules NS/B<k>.lean")
    ap.add_argument("--leafmatch", default="", help="leaf_match.tsv (written by s26_leafmatch.py): the run's leaves (pl, T2 index i); "
                    "LF = membership in that list, hLF by BCP.t2match against T2.leaves_c (identity permutation)")
    ap.add_argument("--tbits", type=int, default=250000, help="piece bits per block-check theorem")
    ap.add_argument("--mbits", type=int, default=2000000, help="piece bits per block-check module")
    a = ap.parse_args()
    ipsha, sdsha = sha(a.ip)[:16], sha(a.table)[:16]
    classes = read_classes(a.table)
    # the run's leaves from leaf_match.tsv: (pl, index in T2.leaves_c), pl packed with 7-bit labels as in the trace
    LI = []
    if a.leafmatch:
        with open(a.leafmatch) as f:
            hdr = f.readline().rstrip("\n").split("\t")
            ci = {h: i for i, h in enumerate(hdr)}
            seen = {}
            for line in f:
                t = line.rstrip("\n").split("\t")
                if int(t[ci["class"]]) != a.cls:
                    continue
                pl, ix = int(t[ci["pl"]], 16), int(t[ci["i"]])
                req(t[ci["p"]] == ",".join(str(x) for x in range(int(t[ci["n"]]))), "leaf_match: non-identity p")
                req(seen.get(pl, ix) == ix, "leaf_match: one pl with two T2 indices")
                seen[pl] = ix
        LI = sorted(seen.items())
    NC = len(classes)
    ip = IP(a.ip)
    R, N = ip.R, ip.N
    req(1 <= R <= 31, "R")
    log("inputs: IP %s (%s) R=%d N=%d rows=%d G=%d; %d classes (%s)" % (a.src, ipsha, R, N, len(ip.rows), len(ip.G),
                                                                         NC, sdsha))

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
                LB |= 1 << (128 * i + l)
    LBR = 0
    for i in range(9):
        for j in range(127):
            if tb(LB, 128 * i + 126 - j):
                LBR |= 1 << (128 * i + j)
    req(all(tb(LB, 128 * i + l) == ((l < N) and (vt[l] >> i) & 1) for i in range(9) for l in range(127)), "planes")
    req(all(u <= R for u in ip.ub), "label bounds")
    UB = sum(ip.ub[l] << (128 * l) for l in range(N))
    UBR = sum(ip.ub[l] << (128 * (126 - l)) for l in range(N))

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
    log("orbit pass: %d superspaces of E (dim %d), %d point tuples" % (len(found), dimE, npairs))

    # entries
    rowsets = [(k, c, ls, "row") for (k, c, ls) in ip.rows] + \
              [(dimE + 1, ip.ub[l], [l], "lab") for l in range(N)]
    nrows, Ntab = len(ip.rows), len(rowsets)
    req(Ntab <= 1 << 15, "slots above 2^15")
    tab = []
    used = {}
    slack = {}
    bad = []
    for i, (k, cap, ls, kind) in enumerate(rowsets):
        U = rref(list(EB) + [vt[l] for l in ls])
        req(len(U) == k, "slot %d: dim %d, file says %d" % (i, len(U), k))
        Um = spanmask(U)
        req(sorted(l for l in range(N) if tb(Um, vt[l])) == sorted(ls), "slot %d: label set is not S'' / E" % i)
        c, (P, Q) = found[U]
        req(classes[c][0] == k, "slot %d: class dim" % i)
        wP, wQ = INV[P], INV[Q]
        duals = perp(U)
        V = list(U) + duals
        req(len(V) == 9 and cap < 32, "slot %d: fields" % i)
        e = k
        for j, v in enumerate(V):
            e |= v << (4 + 9 * j)
        e |= (cap << 85) | (c << 90) | (wP << 100) | (wQ << 109)
        req(e < 1 << EW, "entry width")
        s = cap + classes[c][2] - R
        slack[s] = slack.get(s, 0) + 1
        if not entryOK(R, cls, isGL, e):
            bad.append((i, kind, k, cap, c, classes[c][2]))
            continue
        req(dualIn(DOM, e), "slot %d: dualIn" % i)
        # the run's hypothesis covers the slot's class: c < nCls and dim c > dim E (RunHyp, Tab2/Induct.lean)
        req(c < NC and len(classes[c][1]) > len(basE), "slot %d: class %d not above E" % (i, c))
        mask = sum(1 << l for l in ls)
        rev = sum(1 << (126 - l) for l in ls)
        # labels >= N lie in every row (their planes are 0), as in conv_e1g.py's slot_value
        hi = M127 ^ ((1 << N) - 1)
        lo = (1 << (127 - N)) - 1
        req(slotv(LB, LBR, e) == (mask | hi) | ((rev | lo) << 127) | (cap << 254), "slot %d: slot value" % i)
        used[c] = used.get(c, 0) + 1
        tab.append(e)
    if bad:
        for b in bad[:20]:
            print("BAD slot %d (%s): dim %d cap %d class %d lb %d" % b)
        raise Fail("%d slots fail entryOK (first 20 above)" % len(bad))
    for l in range(N):
        e = tab[nrows + l]
        sv = slotv(LB, LBR, e)
        req((sv % (1 << 127)) % (1 << N) == 1 << l and (sv >> 254) % 32 == ip.ub[l], "capslot %d" % l)
    log("entries: %d slots (%d rows + %d label bounds), %d classes used, slack %s" % (
        Ntab, nrows, N, len(used), " ".join("%d:%d" % kv for kv in sorted(slack.items()))))

    # group witnesses
    stabE = [(P, Q) for P in GL for Q in GL if all(tb(Em, actF(P, Q, e)) for e in EB)]
    GE = []
    for gi, pi in enumerate(ip.G):
        w = None
        for P, Q in stabE:
            if all(tb(Em, actF(P, Q, vt[l]) ^ vt[pi[l]]) for l in range(N)):
                w = (P, Q)
                break
        req(w is not None, "group element %d: no witness in Stab(E)" % gi)
        P, Q = w
        req(isGL(P) and isGL(Q), "GE gl")
        req(all(tb(Em, actF(P, Q, x)) == tb(Em, x) for x in range(512)), "GE fixE")
        req(all(pi[l] < N and tb(Em, actF(P, Q, vt[l]) ^ vt[pi[l]]) for l in range(N)), "GE lab")
        GE.append(w)
    NG = len(ip.G)
    GPT = 0
    GET = 0
    for g, pi in enumerate(ip.G):
        GPT |= sum(pi[l] << (7 * l) for l in range(N)) << (889 * g)
        GET |= (GE[g][0] | (GE[g][1] << 9)) << (18 * g)
    log("group: %d permutations, |Stab(E)| = %d, all witnessed" % (NG, len(stabE)))

    # ---------------------------------------------------------------------------------------- Lean modules
    NS = a.ns
    PEND = [] if a.single else None

    def out(path, text):
        if PEND is None:
            emit(path, text)
        else:
            PEND.append((path, text))

    gen = "a script"
    nch = (Ntab + CHUNK - 1) // CHUNK
    binsha = {}
    if a.bin:
        # the entry and slot tables as binary files in the run directory, loaded by #rttablew (B334/E1x/Load.lean)
        req(a.binrel != "", "--bin needs --binrel")
        slots = [slotv(LB, LBR, e) for e in tab]
        for nm, w, vals in (("tab", 15, tab), ("sl", 33, slots)):
            data = b"".join(v.to_bytes(w, "little") for v in vals)
            with open("%s_%s.bin" % (nm, NS), "wb") as f:
                f.write(data)
            binsha[nm] = hashlib.sha256(data).hexdigest()[:16]
        log("tables: tab_%s.bin (%s), sl_%s.bin (%s) in %s" % (NS, binsha["tab"], NS, binsha["sl"], os.getcwd()))
    o = []
    o.append("import B334.E1x.SlotG\n")
    if a.bin:
        o.append("import B334.E1x.Load\n")
    o.append("\n")
    o.append("/-! # E1G data of the IP of class %d (R = %d), generated by %s\n\n" % (a.cls, R, gen))
    o.append("`E` is the span of the class basis `%s`.\n" % ",".join(map(str, basE)))
    o.append("* `VT`: the label representatives (9-bit fields); `LB`, `LBR`: the label planes (plane `i` = bit `i` of "
             "every\n  representative, 128 bits per plane; `LBR` reversed); `DOM`: the nonzero functionals vanishing "
             "on `E`; `Em`: `E`.\n")
    o.append("* `UB`, `UBR`: the label bounds (128-bit fields; `UBR` reversed).\n")
    o.append("* `GP g`: the IP's %d label permutations (7-bit fields; the identity first), padded with element 0 to "
             "2048;\n  `GE g`: a witness `(P, Q)` in G₀ inducing `GP g`.\n" % NG)
    o.append("* `tab i`: the row-table entry of slot `i` (layout of `RT9.lean`): slot `i < nrows` is the `i`-th "
             "multi-label row\n  of the file, slot `nrows + l` the label bound of `l`. `sl` is the slot function of "
             "the replay.")
    if a.bin:
        o.append("\n* Both are loaded from binary data files (`#rttablew`, chunks of 512):"
                 "\n  `tab_%s.bin` (15-byte entries, sha256 %s) and `sl_%s.bin` (33-byte slots, sha256 %s); the facts"
                 "\n  check `sl i = SlotG.slot LB LBR (tab i)` for every slot. -/\n\n" % (NS, binsha["tab"], NS, binsha["sl"]))
        o.append("#rttablew B334.E1x.%s.TBT \"%s/tab_%s.bin\" 512 120\n" % (NS, a.binrel, NS))
        o.append("#rttablew B334.E1x.%s.SLT \"%s/sl_%s.bin\" 512 264\n" % (NS, a.binrel, NS))
        if a.blkbin:
            o.append("/- the block literal of the run's trace (converted by a script): `BLK.L0` -/\n")
            o.append("#e1lits B334.E1x.%s.BLK \"%s/%s\"\n" % (NS, a.binrel, a.blkbin))
        o.append("\n")
    else:
        req(not a.blkbin, "--blkbin needs --bin")
        o.append(" Core Lean. -/\n\n")
    o.append("namespace B334.E1x.%s\n\nnoncomputable section\n\n" % NS)
    o.append("def R : Nat := %d\ndef N : Nat := %d\n" % (R, N))
    for nm, v in (("VT", VT), ("Em", Em), ("DOM", DOM), ("LB", LB), ("LBR", LBR), ("UB", UB), ("UBR", UBR)):
        o.append("def %s : Nat := %s\n" % (nm, hx(v)))
    o.append("def NG : Nat := %d\n" % NG)
    o.append("def GPT : Nat := %s\n" % hx(GPT))
    o.append("def GET : Nat := %s\n" % hx(GET))
    o.append("def GP (g : Nat) : Nat := (GPT >>> (889 * (if g < NG then g else 0))) % 2 ^ 889\n")
    o.append("def GE (g : Nat) : Nat × Nat :=\n  ((GET >>> (18 * (if g < NG then g else 0))) % 512, "
             "(GET >>> (18 * (if g < NG then g else 0) + 9)) % 512)\n")
    o.append("def Ntab : Nat := %d\ndef nrows : Nat := %d\n\n" % (Ntab, nrows))
    if a.bin:
        o.append("def tab (i : Nat) : Nat := TBT.entry i\n")
        o.append("def sl (i : Nat) : Nat := if i < Ntab then SLT.entry i else 0\n")
    else:
        for k in range(nch):
            v = 0
            for j, e in enumerate(tab[CHUNK * k:CHUNK * (k + 1)]):
                v |= e << (EW * j)
            o.append("def T%d : Nat := %s\n" % (k, hx(v)))
        o.append("\n/-- the literal holding slots `512 k … 512 k + 511` -/\n")
        o.append("def tchunk (k : Nat) : Nat :=\n  %s\n" % tree(0, nch, "T"))
        o.append("def tab (i : Nat) : Nat := (tchunk (i / 512) >>> (118 * (i % 512))) % 2 ^ 118\n")
        o.append("def sl (i : Nat) : Nat := if i < Ntab then SlotG.slot LB LBR (tab i) else 0\n")
    if LI:
        o.append("/-- the run's leaves (packed prefix, index of the covering record in `T2.leaves_%d`) -/\n" % a.cls)
        o.append("def LI : List (Nat × Nat) := [%s]\n" % ", ".join("(0x%x, %d)" % q for q in LI))
        o.append("def LFn (pl : Nat) : Bool := LI.any (fun q => Nat.beq q.1 pl)\n")
    else:
        o.append("def LFn (_pl : Nat) : Bool := false\n")
    o.append("def C : E1G.Ctx := { R := R, N := N, VT := VT, DOM := DOM, GP := GP, LF := LFn }\n\n")
    o.append("end\n\nend B334.E1x.%s\n" % NS)
    out("B334/E1x/%s/Data.lean" % NS, "".join(o))

    out("B334/E1x/%s/Base.lean" % NS, """import B334.E1x.%(NS)s.Data
import B334.E1x.RTE
import B334.E1x.ClsTab
import B334.E1x.IPChk
import B334.Tab2.Data

/-! # The per-slot check of `%(NS)s` (generated by %(gen)s): the entry's dual vectors lie in the domain, the entry
passes `RT.entryOK` against the class table `ClsTab.CL`, and its class is one the run's hypothesis covers (`c < nCls`
and of larger dimension than the run's class %(cls)d, as in `RunHyp`, `Tab2/Induct.lean`). -/

namespace B334.E1x.%(NS)s

noncomputable def entF (i : Nat) : Bool :=
  SlotG.dualIn DOM (tab i) && RT.entryOK R ClsTab.CL (tab i) && %(sleq)sNat.blt (RT.eCls (tab i)) Tab2.nCls &&
    Nat.blt (Tab2.basisOf %(cls)d).length (Tab2.basisOf (RT.eCls (tab i))).length

end B334.E1x.%(NS)s
""" % {"NS": NS, "gen": gen, "cls": a.cls,
       "sleq": "Nat.beq (sl i) (SlotG.slot LB LBR (tab i)) &&\n    " if a.bin else ""})

    starts = list(range(0, Ntab, CHUNK))
    mods = []
    for mi in range(0, len(starts), a.per):
        grp = starts[mi:mi + a.per]
        nm = "S%d" % (mi // a.per)
        mods.append(nm)
        t = ["import B334.E1x.%s.Base\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n" % NS,
             "/-! # Entry checks of `%s`, slots %d … %d (generated by %s; `decide +kernel`) -/\n\n" % (
                 NS, grp[0], min(Ntab, grp[-1] + CHUNK) - 1, gen),
             "namespace B334.E1x.%s\n\n" % NS]
        for s0 in grp:
            t.append("theorem ok_%d : IPChk.allR entF %d %d = true := by decide +kernel\n" % (
                s0, s0, min(CHUNK, Ntab - s0)))
        t.append("\nend B334.E1x.%s\n" % NS)
        out("B334/E1x/%s/%s.lean" % (NS, nm), "".join(t))

    out("B334/E1x/%s/F.lean" % NS, """import B334.E1x.%(NS)s.Data
import B334.E1x.G.IPB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Structure facts of `%(NS)s` (generated by %(gen)s; `decide +kernel` on the Boolean forms
of `G/IPB.lean`): the fields of `E1GS.IPOK` other than the slot table, and the group elements `g < NG`. -/

namespace B334.E1x.%(NS)s
open B334.E1x.E1GS

theorem N_le : N ≤ 127 := by decide
theorem R_le : R ≤ 31 := by decide
theorem R_pos : 1 ≤ R := by decide
theorem DOM_lt : DOM < 2 ^ 512 := by decide +kernel
theorem cosets : Cosets Em VT N := cosets_of (by decide +kernel)
theorem domperp : DomPerp DOM Em := domperp_of (by decide +kernel)
theorem planes : Planes LB VT N := planes_of (by decide +kernel)
theorem planesR : PlanesR LB LBR := planesR_of (by decide +kernel)
theorem Ntab_le : Ntab ≤ 2 ^ 15 := by decide
theorem capslot : ∀ l < N, nrows + l < Ntab ∧ (∀ j < N, (smask (sl (nrows + l))).testBit j = decide (j = l)) ∧
    scap (sl (nrows + l)) = E1G.fld UB l := capslot_of (by decide +kernel)
theorem UB_eq : UB = V (fun l => E1G.fld UB l) := by
  rw [show V (fun l => E1G.fld UB l) = pkL 128 (fun l => E1G.fld UB l) 127 from (pkL_eq _ _ _).symm]; decide +kernel
theorem UBR_eq : UBR = VR (fun l => E1G.fld UB l) := by
  rw [show VR (fun l => E1G.fld UB l) = pkL 128 (fun j => E1G.fld UB (126 - j)) 127 from (pkL_eq _ _ _).symm]
  decide +kernel
theorem UB_le : ∀ l < 127, E1G.fld UB l ≤ 2 ^ 32 := uble_of (by decide +kernel)
theorem grpB : IPChk.allR (fun g => geltB Em VT N (GP g) (GE g).1 (GE g).2) 0 NG = true := by decide +kernel
theorem gelt : ∀ g < NG, GElt Em VT N (GP g) (GE g).1 (GE g).2 := fun g hg => gelt_of (IPChk.allR_spec0 grpB g hg)

end B334.E1x.%(NS)s
""" % {"NS": NS, "gen": gen})

    joins = []
    acc = CHUNK if Ntab > CHUNK else Ntab
    joins.append("  have h0 : IPChk.allR entF 0 %d = true := ok_0\n" % acc)
    for q, s0 in enumerate(starts[1:], 1):
        m = min(CHUNK, Ntab - s0)
        joins.append("  have h%d : IPChk.allR entF 0 %d = true := IPChk.allR_join entF 0 %d %d h%d ok_%d\n" % (
            q, s0 + m, s0, m, q - 1, s0))
    joins.append("  exact h%d\n" % (len(starts) - 1))
    out("B334/E1x/%s/OK.lean" % NS, "".join(["import B334.E1x.%s.%s\n" % (NS, m) for m in mods]) + """import B334.E1x.%(NS)s.F
import B334.E1x.ClsAll

set_option maxRecDepth 100000

/-! # `E1GS.IPOK` and the row bounds of `%(NS)s` (generated by %(gen)s)

`ipok`: every field of `IPOK C Em LB LBR UB UBR Ntab nrows sl tab GE`. `rows`: the `hrow` of `E1GS.e1_sound`, from
the facts of the classes of larger dimension than the run's class %(cls)d (`hhi`, the hypothesis of `RunHyp`,
`Tab2/Induct.lean`) through `RT.rows_of_classes'`. -/

namespace B334.E1x.%(NS)s
open B334.E1x.E1GS

theorem okAll : IPChk.allR entF 0 Ntab = true := by
%(joins)s
theorem ent_all : ∀ i < Ntab, entF i = true := fun i hi => by
  have h := IPChk.allR_spec entF 0 Ntab okAll i hi
  rwa [Nat.zero_add] at h

theorem sl_spec : ∀ i < Ntab, sl i = SlotG.slot LB LBR (tab i) ∧ SlotG.dualIn DOM (tab i) = true := fun i hi => by
  have h := ent_all i hi
  unfold entF at h
  simp only [Bool.and_eq_true] at h
  %(slspec)s

theorem sl_zero : ∀ i, Ntab ≤ i → i < 2 ^ 15 → sl i = 0 := fun i h1 _ => by
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

theorem ipok : IPOK C Em LB LBR UB UBR Ntab nrows sl tab GE where
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

theorem hent : ∀ i < Ntab, RT.entryOK R ClsTab.CL (tab i) = true ∧
    RT.classOK ClsTab.CL Tab2.basisOf Tab2.lbOf (RT.eCls (tab i)) = true ∧
    (RT.eCls (tab i) < Tab2.nCls ∧ (Tab2.basisOf %(cls)d).length < (Tab2.basisOf (RT.eCls (tab i))).length) := by
  intro i hi
  have h := ent_all i hi
  unfold entF at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨%(hentok)s, ClsChk.cls_all _ (by unfold RT.eCls; exact Nat.mod_lt _ (by norm_num)), h.1.2, h.2⟩

/-- the row bounds of the IP from the classes above the run's class -/
theorem rows (hhi : ∀ c', c' < Tab2.nCls → (Tab2.basisOf %(cls)d).length < (Tab2.basisOf c').length →
      Tab2.lbOf c' ≠ 0 → RowValid (Tab2.basisOf c') (Tab2.lbOf c')) :
    ∀ i < Ntab, Fact (RT.dualM (tab i)) (R - RT.eCap (tab i)) :=
  RT.rows_of_classes' R ClsTab.CL Ntab tab Tab2.basisOf Tab2.lbOf
    (fun c => c < Tab2.nCls ∧ (Tab2.basisOf %(cls)d).length < (Tab2.basisOf c).length)
    (fun c hc => ClsChk.basis_lt c hc.1) (fun c hc _ hlb => hhi c hc.1 hc.2 hlb) hent

end B334.E1x.%(NS)s
""" % {"NS": NS, "gen": gen, "joins": "".join(joins), "cls": a.cls,
       "slspec": ("exact ⟨Nat.eq_of_beq_eq_true h.1.1.2, h.1.1.1.1⟩" if a.bin else
                  "exact ⟨by unfold sl; exact if_pos hi, h.1.1.1⟩"),
       "hentok": "h.1.1.1.2" if a.bin else "h.1.1.2"})

    if a.blk or a.blkbin:
        if a.blkbin:
            bimp, blkc = "", "BLK.L0"
        else:
            bimp, blkc = "import B334.E1x.%s\n" % a.blk.rsplit(".", 1)[0], a.blk
        lbE = classes[a.cls][2]
        req(lbE == R + 1, "lbOf %d = %d, not R + 1 = %d: the run theorem needs another shape" % (a.cls, lbE, R + 1))
        X0 = min(X for X in range(1, 512) if tb(DOM, X))
        if a.blkinfo:
            # the run is a list of pieces: block-check modules (pieces packed by bits), glue witnesses W
            req(a.blkbin and not a.single, "--blkinfo needs --blkbin and the module-per-part output")
            bits, W, leaves = [], None, None
            for line in open(a.blkinfo):
                t = line.split()
                if t and t[0] == "piece":
                    req(int(t[1]) == len(bits), "info: piece order")
                    bits.append(int(t[t.index("bits") + 1]))
                elif t and t[0] == "W":
                    W = [[int(x) for x in w.split(",") if x != ""] for w in line[2:].rstrip("\n").split(";")]
                elif t and t[0] == "leaves":
                    leaves = t[1:]
            req(bits and W is not None and len(W) == len(bits), "info: pieces and W")
            req(sorted(int(x, 16) for x in (leaves or [])) == [q[0] for q in LI],
                "the converter's leaves differ from leaf_match.tsv for class %d" % a.cls)
            npc = len(bits)
            thms, cur = [], [0, 0, 0]          # theorem ranges (a, m, bits)
            for i, b in enumerate(bits):
                if cur[1] and cur[2] + b > a.tbits:
                    thms.append(tuple(cur))
                    cur = [i, 0, 0]
                cur[1] += 1
                cur[2] += b
            thms.append(tuple(cur))
            bmods, mcur, mb = [], [], 0
            for th in thms:
                if mcur and mb + th[2] > a.mbits:
                    bmods.append(mcur)
                    mcur, mb = [], 0
                mcur.append(th)
                mb += th[2]
            bmods.append(mcur)
            for k, ths in enumerate(bmods):
                out("B334/E1x/%s/B%d.lean" % (NS, k), "import B334.E1x.%s.Data\nimport B334.E1x.G.Asm\n\n"
                    "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"
                    "/-! # Block pieces %d … %d of `%s` (%d bits; generated by %s; `decide +kernel`) -/\n\n"
                    "namespace B334.E1x.%s\nopen B334.E1x.E1GS\n\n%s\nend B334.E1x.%s\n" % (
                        NS, ths[0][0], ths[-1][0] + ths[-1][1] - 1, NS, sum(t[2] for t in ths), gen, NS,
                        "".join("theorem blk_%d : blkChk C sl UB UBR BLK.lits %d %d = true := by decide +kernel\n" % (
                            t[0], t[0], t[1]) for t in thms if t in ths), NS))
            bimp = "".join("import B334.E1x.%s.B%d\n" % (NS, k) for k in range(len(bmods)))
            jn = ["  have h0 : blkChk C sl UB UBR BLK.lits 0 %d = true := blk_0\n" % thms[0][1]]
            for q in range(1, len(thms)):
                t0, m0 = thms[q][0], thms[q][1]
                jn.append("  have h%d : blkChk C sl UB UBR BLK.lits 0 %d = true :=\n"
                          "    blkChk_join C sl UB UBR BLK.lits 0 %d %d h%d blk_%d\n" % (q, t0 + m0, t0, m0, q - 1, t0))
            jn.append("  exact h%d\n" % (len(thms) - 1))
            # the glue check in its own modules, GLCH pieces per module (Fin only composes)
            out("B334/E1x/%s/Gw.lean" % NS, "import B334.E1x.%s.Data\n\n"
                "/-! # Glue witnesses of the pieces of `%s` (generated by %s): record `j` of piece `i` is glued to "
                "piece `W[i][j]` -/\n\nnamespace B334.E1x.%s\n\ndef W : List (List Nat) := [%s]\n\nend B334.E1x.%s\n" % (
                    NS, NS, gen, NS, ", ".join("[%s]" % ", ".join(str(x) for x in w) for w in W), NS))
            grng = [(lo, min(npc, lo + 200)) for lo in range(0, npc, 200)]
            for q, (lo, hi) in enumerate(grng):
                out("B334/E1x/%s/Gl%d.lean" % (NS, q), "import B334.E1x.%s.Gw\nimport B334.E1x.GJ.ChkB\n\n"
                    "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"
                    "/-! # Glue of the pieces %d … %d of `%s` (generated by %s; core Lean, `decide +kernel`) -/\n\n"
                    "namespace B334.E1x.%s\n\ntheorem gl_%d : IPChk.allR (GJ.glueIB BLK.lits W) %d %d = true := by "
                    "decide +kernel\n\nend B334.E1x.%s\n" % (NS, lo, hi - 1, NS, gen, NS, lo, lo, hi - lo, NS))
                bimp += "import B334.E1x.%s.Gl%d\n" % (NS, q)
            bimp += "import B334.E1x.GJ.JobS\n"
            fgl = "(GJ.glueIB BLK.lits W)"
            gj = ["  have h0 : IPChk.allR %s 0 %d = true := gl_0\n" % (fgl, grng[0][1])]
            for q in range(1, len(grng)):
                lo, hi = grng[q]
                gj.append("  have h%d : IPChk.allR %s 0 %d = true := IPChk.allR_join %s 0 %d %d h%d gl_%d\n" % (
                    q, fgl, hi, fgl, lo, hi - lo, q - 1, lo))
            gj.append("  exact h%d\n" % (len(grng) - 1))
            gluethm = ("theorem glueAll : IPChk.allR %s 0 %d = true := by\n" % (fgl, npc) + "".join(gj) +
                       "theorem glues : glueChk BLK.lits W = true := by rw [GJ.glueChk_eq, nlits]; exact glueAll\n")
            leafthm, hlfarg = leaf_modules(out, NS, gen, a.cls, LI)
            if LI:
                bimp += "".join("import B334.E1x.%s.Lf%d\n" % (NS, q) for q in range((len(LI) + LFCH - 1) // LFCH))
            core = ("theorem nlits : BLK.lits.length = %d := by decide\n" % npc +
                    "theorem blks : blkChk C sl UB UBR BLK.lits 0 %d = true := by\n" % npc + "".join(jn) +
                    "theorem root : BLK.lits.getD 0 0 % 2 ^ 13 = 0 := by decide +kernel\n" + gluethm + "\n" + leafthm +
                    ("theorem concl (hhi : Tab2.HighHyp %d) : E1Concl Em %d :=\n" % (a.cls, R)) +
                    ("  e1_sound C Em LB LBR UB UBR Ntab nrows sl tab GE ipok (rows hhi) %s\n" % hlfarg) +
                    "    BLK.lits (by rw [nlits]; decide) root\n"
                    "    (fun i hi => blkChk_spec C sl UB UBR BLK.lits %d blks i (by rw [nlits] at hi; exact hi))\n" % npc +
                    "    (glueChk_spec BLK.lits W glues)\n")
            what = ("The run is the list `BLK.lits` of %d pieces (by a script: the trace block split into a "
                    "mode-0 root and\nmode-1 / restart pieces), checked in `B0` … `B%d` (`blkChk`) and glued by the "
                    "witness table `W` (`glueChk`)." % (npc, len(bmods) - 1))
        else:
            core = ("theorem blk : E1G.block C sl UB UBR %(blk)s = true := by decide +kernel\n"
                    "theorem root : %(blk)s %% 2 ^ 13 = 0 := by decide +kernel\n"
                    "theorem noglue : E1G.rd 8 (E1G.bS2 %(blk)s) = 0 := by decide +kernel\n\n"
                    "theorem concl (hhi : Tab2.HighHyp %(cls)d) : E1Concl Em %(R)d :=\n"
                    "  e1_sound C Em LB LBR UB UBR Ntab nrows sl tab GE ipok (rows hhi) (fun _ h => by simp [C, LFn] at h)\n"
                    "    [%(blk)s] (by decide) root\n"
                    "    (fun i hi => by\n"
                    "      have hi0 : i = 0 := by simp at hi; omega\n"
                    "      subst hi0\n"
                    "      exact blk)\n"
                    "    (fun i hi j hj => by\n"
                    "      have hi0 : i = 0 := by simp at hi; omega\n"
                    "      subst hi0\n"
                    "      have h0 : E1G.rd 8 (E1G.bS2 ([%(blk)s].getD 0 0)) = 0 := noglue\n"
                    "      exact absurd hj (by rw [h0]; exact Nat.not_lt_zero j))\n") % {
                        "blk": blkc, "cls": a.cls, "R": R}
            what = ("The block literal is `%s` (converter v0 on the run's trace: one block, no glue, no leaves)." %
                    blkc)
        out("B334/E1x/%s/Fin.lean" % NS, """import B334.E1x.%(NS)s.OK
%(bimp)simport B334.E1x.Bridge
import B334.Tab2.Dispatch

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The run of class %(cls)d (R = %(R)d): `E1Concl Em %(R)d` and its row (generated by %(gen)s)

%(what)s It is replayed here
against the IP's own slot function `sl` (slots from the row-table entries). With `ipok` and `rows`, `E1GS.e1_sound`
gives `E1Concl Em %(R)d`; `rowValid_of_e1` (padding, `oneOK`, `emOK`) then gives the class's row at `lbOf %(cls)d = %(R1)d`.
`run_%(cls)d : Tab2.HighHyp %(cls)d → RowValid (Tab2.basisOf %(cls)d) (Tab2.lbOf %(cls)d)` is the form `Tab2/Dispatch.lean` takes. -/

namespace B334.E1x.%(NS)s
open B334.E1x.E1GS

%(core)s
theorem one_ok : oneOK Em %(X0)d = true := by decide +kernel
theorem em_ok : emOK Em (Tab2.basisOf %(cls)d) = true := by decide +kernel
theorem lb_eq : Tab2.lbOf %(cls)d = %(R)d + 1 := by decide

/-- **The run of class %(cls)d** -/
theorem run_%(cls)d (hhi : Tab2.HighHyp %(cls)d) : RowValid (Tab2.basisOf %(cls)d) (Tab2.lbOf %(cls)d) := by
  rw [lb_eq]
  exact rowValid_of_e1 (ClsChk.basis_lt %(cls)d (by decide)) (concl hhi) one_ok em_ok

/-- the run in the dispatcher's list form -/
theorem runsFor : Tab2.RunsFor [%(cls)d] := fun c hc hhi => by
  rw [List.mem_singleton] at hc
  subst hc
  exact run_%(cls)d hhi

end B334.E1x.%(NS)s
""" % {"NS": NS, "bimp": bimp, "blk": blkc, "cls": a.cls, "R": R, "R1": R + 1, "X0": X0, "gen": gen,
       "core": core, "what": what})

    if PEND is not None:
        # one module for the whole IP: the imports of all parts (without the IP's own modules), then the bodies
        imps, bodies = [], []
        for _, text in PEND:
            lines = text.split("\n")
            k = 0
            while k < len(lines) and lines[k].startswith("import "):
                if not lines[k].startswith("import B334.E1x.%s." % NS) and lines[k] not in imps:
                    imps.append(lines[k])
                k += 1
            bodies.append("\n".join(lines[k:]).strip("\n") + "\n")
        emit("B334/E1x/%s/All.lean" % NS, "\n".join(imps) + "\n\n" + "\n".join(bodies))

    if a.glob:
        emit("B334/E1x/ClsTab.lean", """/-! # The class table of ⟨3,3,4⟩ (generated by %(gen)s)

96-bit slots (layout of `RTE.lean`): `[4] n`, `[5] lb`, then `n` 9-bit vectors spanning the annihilator of the class
space (the span of the basis column); `lb` is the `lb_used` column, which is `Tab2.lbOf`. %(nc)d classes. Core Lean. -/

namespace B334.E1x.ClsTab

def CL : Nat := %(cl)s

end B334.E1x.ClsTab
""" % {"gen": gen, "sd": sdsha, "nc": NC, "cl": hx(CL)})
        emit("B334/E1x/ClsBase.lean", """import B334.E1x.RTE
import B334.E1x.ClsTab
import B334.E1x.IPChk
import B334.Tab2.Data

set_option maxHeartbeats 0

/-! # The class check (generated by %(gen)s): `classOK` of the class table against the class data
`B334/Tab2/Data.lean`, and the 9-bit bound of its bases -/

namespace B334.E1x.ClsChk

noncomputable def clsF (c : Nat) : Bool := RT.classOK ClsTab.CL Tab2.basisOf Tab2.lbOf c

theorem basisB : IPChk.allR (fun c => (Tab2.basisOf c).all (fun b => Nat.blt b (2 ^ 9))) 0 Tab2.nCls = true := by
  decide +kernel

theorem basis_lt : ∀ c < Tab2.nCls, ∀ b ∈ Tab2.basisOf c, b < 2 ^ 9 := fun c hc b hb => by
  have h : (Tab2.basisOf c).all (fun b => Nat.blt b (2 ^ 9)) = true := IPChk.allR_spec0 basisB c hc
  rw [List.all_eq_true] at h
  have h2 : Nat.blt b (2 ^ 9) = true := h b hb
  rwa [Nat.blt_eq] at h2

end B334.E1x.ClsChk
""" % {"gen": gen})
        # equal ranges of real classes (kernel memory grows with the classes per fact: 309 classes took 13.6 GB);
        # the indices from NC to 1023 have bound 0 and cost nothing
        step = -(-NC // a.cmods)
        bounds = list(range(0, NC, step))[:a.cmods] + [1024]
        cm = []
        for k in range(len(bounds) - 1):
            lo, hi = bounds[k], bounds[k + 1]
            cm.append((lo, hi))
            emit("B334/E1x/ClsOK%d.lean" % k, """import B334.E1x.ClsBase

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Class check, classes %(lo)d … %(hi1)d (generated by %(gen)s; `decide +kernel`) -/

namespace B334.E1x.ClsChk

theorem cls_%(lo)d : IPChk.allR clsF %(lo)d %(m)d = true := by decide +kernel

end B334.E1x.ClsChk
""" % {"lo": lo, "hi1": hi - 1, "m": hi - lo, "gen": gen})
        jn = ["  have h0 : IPChk.allR clsF 0 %d = true := cls_0\n" % cm[0][1]]
        for q in range(1, len(cm)):
            lo, hi = cm[q]
            jn.append("  have h%d : IPChk.allR clsF 0 %d = true := IPChk.allR_join clsF 0 %d %d h%d cls_%d\n" % (
                q, hi, lo, hi - lo, q - 1, lo))
        emit("B334/E1x/ClsAll.lean", "".join("import B334.E1x.ClsOK%d\n" % k for k in range(len(cm))) + """
/-! # The class check for every class index (generated by %(gen)s) -/

namespace B334.E1x.ClsChk

theorem cls_join : IPChk.allR clsF 0 1024 = true := by
%(jn)s  exact h%(last)d

theorem cls_all : ∀ c < 1024, RT.classOK ClsTab.CL Tab2.basisOf Tab2.lbOf c = true := fun c hc => by
  have h := IPChk.allR_spec clsF 0 1024 cls_join c hc
  rw [Nat.zero_add] at h
  exact h

end B334.E1x.ClsChk
""" % {"gen": gen, "jn": "".join(jn), "last": len(cm) - 1})

    print("=== SUMMARY")
    print("ip %s sha %s table sha %s class %d R %d N %d dimE %d" % (a.src, ipsha, sdsha, a.cls, R, N, dimE))
    print("slots %d rows %d labels %d chunks %d modules %s" % (Ntab, nrows, N, nch, ",".join(mods)))
    print("classes used %d: %s" % (len(used), " ".join("%d:%d" % kv for kv in sorted(used.items()))))
    print("slack (cap + lb - R): %s" % " ".join("%d:%d" % kv for kv in sorted(slack.items())))
    print("group %d stabE %d" % (NG, len(stabE)))
    print("tab sha256 %s" % hashlib.sha256(b"".join(e.to_bytes(15, "little") for e in tab)).hexdigest()[:16])
    log("done")


if __name__ == "__main__":
    try:
        main()
    except Fail as ex:
        print("FAIL: %s" % ex)
        sys.exit(1)
