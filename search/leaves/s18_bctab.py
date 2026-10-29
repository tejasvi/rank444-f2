#!/usr/bin/env python3
"""s18_bctab.py OUT_LEAN [SYMTAB] : the literal tables of the Lean checker BranchCheck334 (stream format v5c-334), written as the core-Lean module B334/BC/Tables334.lean (namespace B334.BCT), with self-checks.

Conventions: first factors and functionals are 9-bit (x = 3i+j); b is 12-bit (bit 4j+k = entry (j,k) of
a 3x4 matrix), c is 12-bit (bit 3k+i = entry (k,i) of a 4x3 matrix); T(X)[y][z] = sum_x X_x T[x][y][z] with
T[x][y][z] = 1 iff x = 3i+j, y = 4j+k, z = 3k+i.  A packed 12x12 matrix has 12 slots of 24 bits: the low 12 bits of slot
z are data (column z, or row z), the high 12 bits the identity half (e_z at the start).  Masks over B or C are 4096-bit
(bit v set iff the 12-bit vector v is in the set).

Self-checks (every one must pass, or nothing is written):
  (1) rank T(X) = 4 rank(X as a 3x3 matrix) for all X;
  (2) the root records: the elimination below (the same steps as the Lean code `B334.BC.stepE`) of the column-packed T(X)
      is accepted by elimOk, its rank is rank T(X), lmC gives the column space and kerM the row space of T(X) (computed
      as spans), xof inverts T(X) on the columns of T(X), and <gof(c), v> = <c, xof(v)> on bases of row and column space;
  (3) the same on 1300 random 12x12 matrices (100 of each rank 0 .. 12), packed by columns and by rows (as resC and
      resR do);
  (4) nperp by the doubling recursion equals the direct definition {w : parity(v & w) = 1} for every v < 4096;
  (5) ORBM and CORB_o are read from SYMTAB (default symtab334.tsv; the source of B334.Tab, written by table/s13_gen_symtab.py) and
      recomputed here by brute force over GL4(F2) (orbit minima, as chk334c does); they must agree;
  (6) the packing of every literal is re-read (each table entry extracted as the Lean code does);
  (7) the perp tables NPL, PL, NPH (64 entries each) give nperp and perp of the doubling recursion for every v < 4096.
"""
import random
import sys

SYMTAB = sys.argv[2] if len(sys.argv) > 2 else 'symtab334.tsv'
W = 24                                    # slot width
REP24 = sum(1 << (W * z) for z in range(12))
M24 = (1 << W) - 1
M288 = (1 << (12 * W)) - 1
ID24 = sum(1 << (W * z + 12 + z) for z in range(12))
C23 = sum(1 << (23 * i) for i in range(12))
LEFT12 = sum(0xfff << (W * z) for z in range(12))
HM12 = sum(((0xfff >> (h + 1)) << (h + 1)) << (W * h) for h in range(12))
MAGIC24 = sum(1 << (253 - 23 * k) for k in range(12))
RH12 = 0xfff << 12
REPR24 = sum(1 << (W * z + 12) for z in range(12))
M4096 = (1 << 4096) - 1
ALLNZ = M4096 - 1
M512 = (1 << 512) - 1
C31 = sum(1 << (31 * i) for i in range(9))
M32B = sum(1 << (32 * j) for j in range(9))
M32 = (1 << 32) - 1


def par(v):
    return bin(v).count('1') & 1


def rank(rows):
    a = [r for r in rows if r]
    r = 0
    for bit in range(12):
        p = next((i for i in range(r, len(a)) if (a[i] >> bit) & 1), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        for i in range(len(a)):
            if i != r and (a[i] >> bit) & 1:
                a[i] ^= a[r]
        r += 1
    return r


def span_mask(gens):
    el = [0]
    seen = {0}
    for g in gens:
        if g in seen:
            continue
        new = [e ^ g for e in el]
        el += new
        seen.update(new)
    m = 0
    for e in el:
        m |= 1 << e
    return m


def transpose(rows):
    return [sum(((rows[y] >> z) & 1) << y for y in range(12)) for z in range(12)]


# ---------------------------------------------------------------- the Lean code's bit-level functions, emulated
def spr24(c):
    return (c * C23) & REP24


def nperp(v):                              # the doubling recursion of B334.BC.nperp
    N = 0
    for k in range(12):
        N = N | ((N ^ (((v >> k) & 1) * ((1 << (1 << k)) - 1))) << (1 << k))
    return N


def perp(v):
    return M4096 ^ nperp(v)


def stepE(h, s):
    P, PM, rk, DG, D24, M = s
    cand = (M >> h) & REP24
    if cand == 0:
        return s
    p = (M // (cand ^ (cand & (cand - 1)))) & M24
    return ((P ^ (((P >> h) & REP24) * p)) | (p << (W * h)), PM | (1 << h), rk + 1, DG | (1 << (25 * h)),
            D24 | (1 << (W * h)), M ^ (cand * p))


def elim(M):
    s = (0, 0, 0, 0, 0, M)
    for h in range(11, -1, -1):
        s = stepE(h, s)
    return s


def elimOk(s):
    P, PM, rk, DG, D24, M = s
    return (M & LEFT12) == 0 and (P & HM12) == 0 and (P & (PM * REP24)) == DG and (P & (D24 * M24)) == P


def gather(P, j):
    return ((((P >> j) & REP24) * MAGIC24) >> 253) & 4095


def lmC(P, PM):
    acc = M4096
    for j in range(11, -1, -1):
        if not (PM >> j) & 1:
            acc &= perp(gather(P, j) | (1 << j))
    return acc


def kerM(M):
    acc = M4096
    for z in range(11, -1, -1):
        sl = (M >> (W * z)) & M24
        if sl != 0:
            acc &= perp(sl >> 12)
    return acc


def xof(P, b):
    y0 = P & (spr24(b) * RH12)
    y1 = y0 ^ (y0 >> 192)
    y2 = y1 ^ (y1 >> 96)
    y3 = y2 ^ (y2 >> 48)
    return ((y3 ^ (y3 >> 24)) >> 12) & 4095


def gof(P, c):
    q = P & (c * REPR24)
    q1 = q ^ (q >> 1)
    q2 = q1 ^ (q1 >> 2)
    q3 = q2 ^ (q2 >> 4)
    return gather(q3 ^ (q2 >> 8), 12)


def mv(rows, x):                           # (R x)_y = parity(row_y & x)
    return sum(par(rows[y] & x) << y for y in range(12))


def pack(vecs):
    return sum(v << (W * i) for i, v in enumerate(vecs))


def check_matrix(rows, what):
    """the checks (2)/(3) for one 12x12 matrix given by its rows (masks over z)"""
    cols = transpose(rows)
    rk = rank(rows)
    colm, rowm = span_mask(cols), span_mask(rows)
    s = elim(pack(cols) ^ ID24)
    P, PM, rkE, DG, D24, M = s
    assert elimOk(s), (what, 'elimOk')
    assert rkE == rk, (what, 'rank', rkE, rk)
    assert lmC(P, PM) == colm, (what, 'lmC')
    assert kerM(M) == rowm, (what, 'kerM')
    for z in range(12):                   # x inverts R on col R (on the columns, hence on their span: xof is linear)
        assert mv(rows, xof(P, cols[z])) == cols[z], (what, 'xof', z)
    rb = [r for r in rows if r]
    for c in rb:                           # <g(c), v> = <c, x(v)> for c in row R, v in col R (bases)
        g = gof(P, c)
        for v in cols:
            assert par(g & v) == par(c & xof(P, v)), (what, 'gof')
    s2 = elim(pack(rows) ^ ID24)           # packed by rows (resR): kerM gives col R
    assert elimOk(s2) and s2[2] == rk and kerM(s2[5]) == colm, (what, 'rows')
    return s


def main():
    out = sys.argv[1]
    # ---- T334 slices
    TXrow = [[0] * 12 for _ in range(512)]
    for X in range(512):
        for i in range(3):
            for j in range(3):
                for k in range(4):
                    x, y, z = 3 * i + j, 4 * j + k, 3 * k + i
                    if (X >> x) & 1:
                        TXrow[X][y] ^= 1 << z
    TXcol = [transpose(TXrow[X]) for X in range(512)]
    # (1)
    for X in range(512):
        r3 = [(X >> (3 * i)) & 7 for i in range(3)]
        assert rank(TXrow[X]) == 4 * rank(r3), X
    # (2) root records
    RPT = RKT = LIDX = RIDX = 0
    lcls, rcls = [], []
    for X in range(512):
        P, PM, rk, DG, D24, M = check_matrix(TXrow[X], 'T(X=%d)' % X)
        RPT |= (P | (PM << 288) | (rk << 300)) << (304 * X)
        RKT |= rk << (4 * X)
        lm, rm = span_mask(TXcol[X]), span_mask(TXrow[X])
        if lm not in lcls:
            lcls.append(lm)
        if rm not in rcls:
            rcls.append(rm)
        LIDX |= lcls.index(lm) << (4 * X)
        RIDX |= rcls.index(rm) << (4 * X)
    assert len(lcls) == 16 and len(rcls) == 16, (len(lcls), len(rcls))
    LMV = sum(m << (4096 * i) for i, m in enumerate(lcls))
    RMV = sum(m << (4096 * i) for i, m in enumerate(rcls))
    # (3) random matrices of every rank
    rng = random.Random(334)
    for trial in range(1300):
        r = trial % 13
        A = [rng.randrange(4096) for _ in range(r)]
        B = [rng.randrange(4096) for _ in range(r)]
        rows = [0] * 12
        for t in range(r):                 # R = sum_t a_t b_t^T has rank <= r
            for y in range(12):
                if (A[t] >> y) & 1:
                    rows[y] ^= B[t]
        check_matrix(rows, 'random %d' % trial)
    # (4) nperp
    for v in range(4096):
        d = 0
        for w in range(4096):
            if par(v & w):
                d |= 1 << w
        assert nperp(v) == d, v
    # (5) ORBM / CORB from the TSV, recomputed by brute force
    orbl, corb = None, {}
    for line in open(SYMTAB):
        f = line.rstrip('\n').split('\t')
        if f[0] == 'ORBM':
            orbl = [int(x) for x in f[2].split(',')]
        elif f[0] == 'CORB':
            corb[int(f[1])] = [int(x) for x in f[2].split(',')]
    assert orbl is not None and len(orbl) == 15 and sorted(corb) == sorted(orbl)

    def m44(u, v):
        out = 0
        for r in range(4):
            acc = 0
            for l in range(4):
                if (u >> (4 * r + l)) & 1:
                    acc ^= (v >> (4 * l)) & 15
            out |= acc << (4 * r)
        return out

    def actB(b, S):                        # b S (3x4 times 4x4)
        out = 0
        for j in range(3):
            acc = 0
            for l in range(4):
                if (b >> (4 * j + l)) & 1:
                    acc ^= (S >> (4 * l)) & 15
            out |= acc << (4 * j)
        return out

    def actC(c, Si):                       # S^-1 c (4x4 times 4x3)
        out = 0
        for k in range(4):
            acc = 0
            for m in range(4):
                if (Si >> (4 * k + m)) & 1:
                    acc ^= (c >> (3 * m)) & 7
            out |= acc << (3 * k)
        return out
    gl = {}                                # all of GL4(F2), each with its inverse (by elimination)

    def inv4(S):
        a = [(S >> (4 * r)) & 15 for r in range(4)]
        e = [1 << r for r in range(4)]
        for col in range(4):
            p = next((r for r in range(col, 4) if (a[r] >> col) & 1), None)
            if p is None:
                return None
            a[col], a[p] = a[p], a[col]
            e[col], e[p] = e[p], e[col]
            for r in range(4):
                if r != col and (a[r] >> col) & 1:
                    a[r] ^= a[col]
                    e[r] ^= e[col]
        return sum(x << (4 * r) for r, x in enumerate(e))
    for S in range(1 << 16):
        Si = inv4(S)
        if Si is not None:
            gl[S] = Si
    assert len(gl) == 20160
    assert all(m44(S, Si) == 0x8421 for S, Si in gl.items())
    seen = bytearray(4096)
    orb_bf = []
    for b in range(1, 4096):
        if seen[b]:
            continue
        orb_bf.append(b)
        for S in gl:
            seen[actB(b, S)] = 1
    assert orb_bf == orbl, (orb_bf, orbl)
    for o in orbl:
        stab = [S for S in gl if actB(o, S) == o]
        sc = bytearray(4096)
        mins = []
        for c in range(1, 4096):
            if sc[c]:
                continue
            mins.append(c)
            for S in stab:
                sc[actC(c, gl[S])] = 1
        assert mins == corb[o], o
    ORBM = sum(1 << b for b in orbl)
    CORBM = {o: sum(1 << c for c in corb[o]) for o in orbl}
    # ---- the literal tables
    PAR = sum(1 << v for v in range(512) if par(v))
    POP11 = sum(bin(x).count('1') << (4 * x) for x in range(2048))
    TXC24 = sum(pack(TXcol[X]) << (288 * X) for X in range(512))
    TXR24 = sum(pack(TXrow[X]) << (288 * X) for X in range(512))
    # (6) re-read every packed entry as the Lean code does
    for X in range(512):
        assert (TXC24 >> (288 * X)) & M288 == pack(TXcol[X])
        assert (TXR24 >> (288 * X)) & M288 == pack(TXrow[X])
        e = (RPT >> (304 * X)) & ((1 << 304) - 1)
        P, PM, rk = e & M288, (e >> 288) & 4095, (e >> 300) & 15
        s = elim(pack(TXcol[X]) ^ ID24)
        assert (P, PM, rk) == (s[0], s[1], s[2]) and (RKT >> (4 * X)) & 15 == rk
        assert (LMV >> (4096 * ((LIDX >> (4 * X)) & 15))) & M4096 == span_mask(TXcol[X])
        assert (RMV >> (4096 * ((RIDX >> (4 * X)) & 15))) & M4096 == span_mask(TXrow[X])
        assert (PAR >> X) & 1 == par(X)
    for x in range(2048):
        assert (POP11 >> (4 * x)) & 15 == bin(x).count('1')
    for v in range(512):                   # dep32 deposits bit i of a 9-bit v at 32 i
        assert (v * C31) & M32B == sum(((v >> i) & 1) << (32 * i) for i in range(9))
    for c in range(4096):
        assert spr24(c) == sum(((c >> z) & 1) << (W * z) for z in range(12))
    # ---- write
    def lit(name, val, doc):
        return ['/-- %s -/' % doc, 'def %s : Nat := 0x%x' % (name, val)]
    L = ['/-! # Literal tables of the Lean checker BranchCheck334 (v5c-334). GENERATED by a script; do not edit.',
         '',
         'Packed 12x12 matrices: 12 slots of 24 bits, the low 12 bits data, the high 12 the identity half. Masks over B or C',
         'are 4096-bit. First factors and functionals are 9-bit. `ORBM` and `CORB_o` are the literals of `B334.Tab.ORBM` and',
         '`B334.Tab.CORB_o` (same source); `corbM b` is `CORB_b` for `b` in `ORBL`, all ones',
         'elsewhere (v7). -/', '', 'namespace B334.BCT', '']
    L += lit('PAR', PAR, 'bit v = parity of v (v < 512)')
    L += lit('TXC24', TXC24, 'T(X) by columns: column z (a mask over y) in bits 288X + 24z .. +11')
    L += lit('TXR24', TXR24, 'T(X) by rows: row y (a mask over z) in bits 288X + 24y .. +11')
    L += lit('M24', M24, '2^24 - 1')
    L += lit('M288', M288, '2^288 - 1')
    L += lit('M512', M512, '2^512 - 1')
    L += lit('M4096', M4096, '2^4096 - 1')
    L += lit('ALLNZ', ALLNZ, 'bits 1 .. 4095 (the nonzero 12-bit vectors)')
    L += lit('REP24', REP24, 'sum_z 2^(24z), z < 12')
    L += lit('LEFT12', LEFT12, 'the data halves (bits 0 .. 11) of the twelve 24-bit slots')
    L += lit('ID24', ID24, 'e_z in the identity half of slot z (bit 24z + 12 + z)')
    L += lit('HM12', HM12, 'slot h: data bits above h')
    L += lit('MAGIC24', MAGIC24, 'sum_k 2^(253 - 23k): multiplying moves bit 24h to bit 253 + h (no carries)')
    L += lit('RH12', RH12, '4095 * 2^12, the identity half of one slot')
    L += lit('REPR24', REPR24, 'sum_z 2^(24z + 12)')
    L += lit('C23', C23, 'sum_i 2^(23i), i < 12: c * C23 &&& REP24 deposits bit z of c at 24z')
    L += lit('C31', C31, 'sum_i 2^(31i), i < 9: x * C31 &&& M32B deposits bit i of x at 32i')
    L += lit('M32B', M32B, 'sum_j 2^(32j), j < 9')
    L += lit('M32', M32, '2^32 - 1')
    L += lit('POP11', POP11, 'popcount of x < 2048, at bits 4x')
    L += lit('RKT', RKT, 'rank of T(X) (4 bits at 4X)')
    L += lit('RPT', RPT, 'root records: P | PM << 288 | rk << 300, at bits 304X (the elimination of the column-packed T(X))')
    L += lit('LIDX', LIDX, 'root column-space class of X (4 bits at 4X)')
    L += lit('RIDX', RIDX, 'root row-space class of X (4 bits at 4X)')
    L += lit('LMV', LMV, 'the 16 root column-space masks, at bits 4096i')
    L += lit('RMV', RMV, 'the 16 root row-space masks, at bits 4096i')
    L += lit('ORBM', ORBM, 'the 15 orbit minima of the nonzero b under b -> b S, S in GL4(F2) (= B334.Tab.ORBM)')
    L += ['def ORBL : List Nat := [%s]' % ', '.join(map(str, orbl))]
    for o in orbl:
        L += lit('CORB_%d' % o, CORBM[o], 'the orbit minima of the nonzero c under c -> S^-1 c, S in Stab(%d) (= B334.Tab.CORB_%d)' % (o, o))
    L += ['/-- `CORB_b` for `b` in `ORBL`, all ones elsewhere (v7 `corbM`) -/', 'def corbM (b : Nat) : Nat :=']
    for o in orbl:
        L.append('  if b = %d then CORB_%d else' % (o, o))
    L += ['  M4096', '']
    # perp tables: nperp v = NPL[v & 63] xor NPH[v >> 6], perp v = PL[v & 63] xor NPH[v >> 6]
    def nset(v):
        m = 0
        for w in range(4096):
            if par(v & w):
                m |= 1 << w
        return m
    NPL = [nset(k) for k in range(64)]
    NPH = [nset(k << 6) for k in range(64)]
    PL = [M4096 ^ x for x in NPL]
    for v in range(4096):                  # (7) the tables against the doubling recursion (itself checked in (4))
        assert NPL[v & 63] ^ NPH[v >> 6] == nperp(v) and PL[v & 63] ^ NPH[v >> 6] == perp(v), v

    # the selection tree: one small definition per internal node (the kernel copies a function body at every call, so a
    # 63-node tree in one body would cost ~30 KB per lookup; small bodies cost ~1 KB)
    def tree_defs(name):
        out = []

        def node(lo, hi):
            if hi - lo == 1:
                return '%s_%d' % (name, lo)
            mid = (lo + hi) // 2
            out.append('def %s_t%d_%d (v : Nat) : Nat := cond (Nat.blt v %d) (%s) (%s)' % (
                name, lo, hi, mid, node(lo, mid) + ('' if mid - lo == 1 else ' v'),
                node(mid, hi) + ('' if hi - mid == 1 else ' v')))
            return '%s_t%d_%d' % (name, lo, hi)
        node(0, 64)
        return out
    L += ['/-! ### perp tables', 'Entry `k < 64`: `NPL_k = {w : parity(k &&& w) = 1}`, `PL_k` its complement, `NPH_k =',
          '{w : parity((k <<< 6) &&& w) = 1}` (masks over `w < 4096`), so `nperp v = NPL[v &&& 63] ^^^ NPH[v >>> 6]` and',
          '`perp v = PL[v &&& 63] ^^^ NPH[v >>> 6]`; an entry is selected by a balanced tree of 6 comparisons, one small',
          'definition per tree node. -/', '']
    for name, tab in (('NPL', NPL), ('PL', PL), ('NPH', NPH)):
        for k in range(64):
            L.append('def %s_%d : Nat := 0x%x' % (name, k, tab[k]))
    for name in ('NPL', 'PL', 'NPH'):
        L += tree_defs(name)
    L += ['/-- `NPL_v` for `v < 64` -/', 'def npl (v : Nat) : Nat := NPL_t0_64 v',
          '/-- `PL_v` for `v < 64` -/', 'def pl (v : Nat) : Nat := PL_t0_64 v',
          '/-- `NPH_v` for `v < 64` -/', 'def nph (v : Nat) : Nat := NPH_t0_64 v', '', 'end B334.BCT']
    with open(out, 'w') as f:
        f.write('\n'.join(L) + '\n')
    print('s18_bctab: all self-checks passed; wrote %s (ORBM %s; CORB sizes %s)' % (out, orbl, [len(corb[o]) for o in orbl]))


if __name__ == '__main__':
    main()
