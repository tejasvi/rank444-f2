#!/usr/bin/env python3
# emit_k.py -- method-K certificate emitter for 21 forced-product rows of <3,3,4> over F2.
# Path A follows the steps of an independent checker of Wang's certificates written for this project (quotient,
# get_slices, fp_plan, build_dense, reduce_dense, make_kprob, fp_kernel).
#
# Single file on purpose (no local imports):
#   python3 -I -B emit_k.py MODE ARGS [--seeded seeded334.tsv] [--certs certs334.tsv]   (defaults: these names in the
#   current directory)
# Modes:
#   explore CLASS...            table over every (p, phi): f nr need reduced size side K killable; path A == path B check
#   emit OUTDIR CLASS...        find a K = 0 certificate per class, write OUTDIR/row<c>.json and OUTDIR/row<c>_neg.json,
#                               re-read the files, run every self-check, refuse the negative
#   check OUTDIR CLASS...       re-run the self-checks on the files already in OUTDIR (no regeneration)
#   summary OUTDIR              write OUTDIR/summary.tsv from the row JSON files
#
# Path A = the checker's steps (0/1 lists, rank-1 u/v form, Aff system).  Path B = matrix form straight from the definition
# (no rank-1 assumption).  Both must agree on the reduced row/column sets and on the killable vectors.
# The self-checks (check_data) use only the emitted JSON data plus the definitions of T334 and of method K, and
# share no code with the generator except par() and rank_masks().
import sys
import os
import json
import itertools
import random
import hashlib

SEEDED, WANG_CERTS = 'seeded334.tsv', 'certs334.tsv'
if '--seeded' in sys.argv:
    _i = sys.argv.index('--seeded'); SEEDED = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
if '--certs' in sys.argv:
    _i = sys.argv.index('--certs'); WANG_CERTS = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
CLASSES = [6, 12, 13, 16, 17, 23, 26, 28, 33, 35, 37, 38, 41, 42, 45, 52, 54, 55, 65, 135, 147]

# expected parameters per class: class -> (dim S, lb, p, f, nr, need, phi, (R, C) after reduction, side, K)
KPAR = {
    6: (7, 12, 1, 4, 4, 8, 'b', (8, 8), 'right', 0),
    12: (7, 16, 1, 8, 4, 8, 'b', (12, 8), 'right', 0),
    13: (7, 16, 1, 8, 4, 8, 'b', (12, 8), 'right', 0),
    16: (7, 16, 1, 4, 8, 12, 'b', (12, 16), 'left', 0),
    17: (7, 16, 1, 8, 4, 8, 'b', (12, 8), 'right', 0),
    23: (6, 16, 1, 8, 4, 8, 'b', (8, 12), 'left', 0),
    26: (6, 16, 1, 8, 4, 8, 'b', (8, 12), 'left', 0),
    28: (6, 16, 1, 8, 4, 8, 'b', (8, 12), 'left', 0),
    33: (6, 16, 1, 4, 4, 12, 'b', (12, 12), 'right', 0),
    35: (6, 20, 1, 8, 4, 12, 'b', (12, 12), 'right', 0),
    37: (6, 16, 2, 8, 4, 8, 'c', (8, 12), 'left', 0),
    38: (6, 20, 2, 8, 4, 12, 'c', (12, 12), 'right', 0),
    41: (6, 16, 2, 8, 4, 8, 'c', (8, 12), 'left', 0),
    42: (6, 20, 1, 8, 4, 12, 'b', (12, 12), 'right', 0),
    45: (6, 20, 1, 8, 4, 12, 'b', (12, 12), 'right', 0),
    52: (6, 20, 2, 8, 4, 12, 'c', (12, 12), 'right', 0),
    54: (6, 16, 1, 8, 4, 8, 'b', (12, 12), 'right', 4),
    55: (6, 16, 1, 4, 8, 12, 'b', (12, 20), 'left', 0),
    65: (6, 16, 1, 8, 4, 8, 'b', (12, 12), 'right', 4),
    135: (5, 20, 2, 8, 4, 12, 'c', (12, 16), 'left', 0),
    147: (5, 20, 1, 8, 4, 12, 'b', (12, 16), 'left', 0),
}
WANG_P = {c: v[2] for c, v in KPAR.items()}
# a hand-picked subset for row 54 (p = 1, flattening (b)): reduced column positions
HAND_SUBSET = {54: (0, 2, 3, 5, 6, 8, 9, 11)}


def par(x):
    return x.bit_count() & 1


def rank_masks(vs):
    basis = {}
    r = 0
    for v in vs:
        while v:
            h = v.bit_length() - 1
            b = basis.get(h)
            if b is None:
                basis[h] = v
                r += 1
                break
            v ^= b
    return r


def pick_bits(mask, idxs):
    r = 0
    for j, i in enumerate(idxs):
        if (mask >> i) & 1:
            r |= 1 << j
    return r


def transpose(M, R, C):
    T = [0] * C
    for r in range(R):
        row = M[r]
        for c in range(C):
            if (row >> c) & 1:
                T[c] |= 1 << r
    return T


# ------------------------------------------------------------------------------------------------ data loading
def load_seeded():
    rows = {}
    with open(SEEDED) as fh:
        hdr = fh.readline().rstrip('\n').split('\t')
        ix = {h: i for i, h in enumerate(hdr)}
        for line in fh:
            t = line.rstrip('\n').split('\t')
            c = int(t[ix['idx']])
            rows[c] = dict(cls=c, dim=int(t[ix['dim']]),
                           basis=[int(x) for x in t[ix['basis']].split(',') if x not in ('-', '')], lb=int(t[ix['seeded']]))
    return rows


def load_wang():
    w = {}
    with open(WANG_CERTS) as fh:
        fh.readline()
        for line in fh:
            t = line.rstrip('\n').split('\t')
            c = int(t[0])
            w[c] = dict(basis=[int(x) for x in t[2].split(',') if x not in ('-', '')], lb=int(t[4]), kind=t[5], params=t[6])
    return w


def load_rows(classes):
    seeded = load_seeded()
    wang = load_wang()
    out = {}
    for c in classes:
        r = seeded[c]
        w = wang[c]
        s = KPAR[c]
        if r['basis'] != w['basis'] or r['lb'] != w['lb']:
            raise SystemExit(f'class {c}: seeded334.tsv and verify_wang/certs334.tsv disagree')
        if w['kind'] != 'forced' or w['params'] != 'proj=%d' % s[2]:
            raise SystemExit(f'class {c}: Wang kind/proj {w["kind"]} {w["params"]} vs expected p={s[2]}')
        if len(r['basis']) != r['dim'] or r['dim'] != s[0] or r['lb'] != s[1]:
            raise SystemExit(f'class {c}: dim/lb disagree with the expected parameters')
        err = check_rref(r['basis'])
        if err:
            raise SystemExit(f'class {c}: basis not RREF: {err}')
        out[c] = r
    return out


def check_rref(basis):
    prev = -1
    for i, r in enumerate(basis):
        if r == 0:
            return 'zero row'
        m = r.bit_length() - 1
        if m <= prev:
            return 'pivots not increasing'
        prev = m
        for j, o in enumerate(basis):
            if j != i and (o >> m) & 1:
                return 'pivot not cleared'
    return ''


# ------------------------------------------------------------------------------------------------ generator (path B)
TT = [[0] * 12 for _ in range(9)]  # TT[a][b] = mask over c
for _i in range(3):
    for _j in range(3):
        for _k in range(4):
            TT[3 * _i + _j][4 * _j + _k] |= 1 << (3 * _k + _i)


def quotient(basis):
    """vw334 quotient: pi[x] bit a = bit np(x) of red(e_a); Q[x][b] = mask over c."""
    piv = {}
    for r in basis:
        piv[r.bit_length() - 1] = r

    def red(v):
        for p in range(8, -1, -1):
            if (v >> p) & 1 and p in piv:
                v ^= piv[p]
        return v

    np_ = [p for p in range(9) if p not in piv]
    na = len(np_)
    pi = [0] * na
    for a in range(9):
        r = red(1 << a)
        for x in range(na):
            if (r >> np_[x]) & 1:
                pi[x] |= 1 << a
    Q = [[0] * 12 for _ in range(na)]
    for x in range(na):
        for a in range(9):
            if (pi[x] >> a) & 1:
                for b in range(12):
                    Q[x][b] ^= TT[a][b]
    return na, np_, pi, Q


def get_slices(Q, na, p):
    """get_slices: U[i][u] = mask over v (mode order)."""
    if p == 0:
        n0, m1, m2 = na, 12, 12
        U = [[Q[x][b] for b in range(12)] for x in range(na)]
    elif p == 1:
        n0, m1, m2 = 12, 12, na
        U = [[0] * 12 for _ in range(12)]  # U[b][c] = mask over x
        for x in range(na):
            for b in range(12):
                for c in range(12):
                    if (Q[x][b] >> c) & 1:
                        U[b][c] |= 1 << x
    else:
        n0, m1, m2 = 12, na, 12
        U = [[0] * na for _ in range(12)]  # U[c][x] = mask over b
        for x in range(na):
            for b in range(12):
                for c in range(12):
                    if (Q[x][b] >> c) & 1:
                        U[c][x] |= 1 << b
    return n0, m1, m2, U


def flat_slice(Ui, m2):
    r = 0
    for u, row in enumerate(Ui):
        r |= row << (u * m2)
    return r


def fp_plan(n0, m1, m2, U):
    """vw334 fp_plan: Fi = rank-1 slices, in index order, that keep the set independent; Ri = every other nonzero slice."""
    Fi, Ri, Fv = [], [], []
    for i in range(n0):
        rk = rank_masks(U[i])
        if rk == 0:
            continue
        fl = flat_slice(U[i], m2)
        if rk == 1 and rank_masks(Fv + [fl]) == len(Fv) + 1:
            Fi.append(i)
            Fv.append(fl)
            continue
        Ri.append(i)
    return Fi, Ri


def build_plan(row, p):
    basis = row['basis']
    na, np_, pi, Q = quotient(basis)
    n0, m1, m2, U = get_slices(Q, na, p)
    Fi, Ri = fp_plan(n0, m1, m2, U)
    return dict(basis=basis, na=na, np=np_, pi=pi, Q=Q, p=p, n0=n0, m1=m1, m2=m2, U=U, Fi=Fi, Ri=Ri, f=len(Fi),
                nr=len(Ri))


def flatten(V, nr, m1, m2, phi):
    """Flattenings.  V = list of nr slices (each a list of m1 row masks over m2 bits).  Returns (R, C, rows-as-masks)."""
    if phi == 'a':
        R, C = nr, m1 * m2
        M = [0] * R
        for s in range(nr):
            for u in range(m1):
                M[s] |= V[s][u] << (u * m2)
    elif phi == 'b':
        R, C = m1, nr * m2
        M = [0] * R
        for s in range(nr):
            for u in range(m1):
                M[u] |= V[s][u] << (s * m2)
    else:
        R, C = m2, nr * m1
        M = [0] * R
        for s in range(nr):
            for u in range(m1):
                row = V[s][u]
                for v in range(m2):
                    if (row >> v) & 1:
                        M[v] |= 1 << (s * m1 + u)
    return R, C, M


def build_flat(plan, phi):
    nr, f, m1, m2, U, Fi, Ri = plan['nr'], plan['f'], plan['m1'], plan['m2'], plan['U'], plan['Fi'], plan['Ri']
    zero = [0] * m1
    R, C, M0 = flatten([U[Ri[s]] for s in range(nr)], nr, m1, m2, phi)
    Ns = []
    for s in range(nr):
        for l in range(f):
            V = [zero] * nr
            V[s] = U[Fi[l]]
            Ns.append(flatten(V, nr, m1, m2, phi)[2])
    return R, C, M0, Ns


def pivot_positions(vecs):
    """Pivot positions (lowest set bit) of the row space of vecs = pivot columns."""
    basis = []
    for v in vecs:
        for lb_, b in basis:
            if (v >> lb_) & 1:
                v ^= b
        if v == 0:
            continue
        l = (v & -v).bit_length() - 1
        for t in basis:
            if (t[1] >> l) & 1:
                t[1] ^= v
        basis.append([l, v])
    return sorted(t[0] for t in basis)


def reduce_matrix(M0, Ns, R, C):
    """vw334 reduce_dense in matrix form.  Returns (rows, cols, M0r, Nr): surviving indices into the full flattening."""
    rows = list(range(R))
    cols = list(range(C))
    M0 = list(M0)
    Ns = [list(N) for N in Ns]
    for _ in range(8):
        changed = False
        vecs = list(M0) + [row for N in Ns for row in N]
        cp = pivot_positions(vecs)
        if len(cp) < len(cols):
            changed = True
            M0 = [pick_bits(r, cp) for r in M0]
            Ns = [[pick_bits(r, cp) for r in N] for N in Ns]
            cols = [cols[c] for c in cp]
        Rc, Cc = len(rows), len(cols)
        vecs = transpose(M0, Rc, Cc)
        for N in Ns:
            vecs += transpose(N, Rc, Cc)
        rp = pivot_positions(vecs)
        if len(rp) < Rc:
            changed = True
            M0 = [M0[r] for r in rp]
            Ns = [[N[r] for r in rp] for N in Ns]
            rows = [rows[r] for r in rp]
        if not changed:
            break
    return rows, cols, M0, Ns


# ---- kernel / witness machinery on (restricted) matrices
def side_vectors(M0, Ns, R, C, side):
    """For z over the kernel side: t(z) = XOR_{j in z} c0[j] and w_m(z) = XOR_{j in z} cN[m][j] are masks over the other side.
    right: z over columns, vectors over rows (M z).  left: z over rows, vectors over columns (z^T M)."""
    if side == 'right':
        return C, R, transpose(M0, R, C), [transpose(N, R, C) for N in Ns]
    return R, C, list(M0), [list(N) for N in Ns]


def xor_table(cols, sd):
    T = [0] * (1 << sd)
    for z in range(1, 1 << sd):
        T[z] = T[z & (z - 1)] ^ cols[(z & -z).bit_length() - 1]
    return T


def witness_for(t, ws):
    """None iff t lies in span(ws).  Otherwise y with y.t = 1 and y.w = 0 for every w in ws (closed form on the RREF basis)."""
    basis = {}
    for w in ws:
        for l, b in basis.items():
            if (w >> l) & 1:
                w ^= b
        if w:
            l = (w & -w).bit_length() - 1
            for k in basis:
                if (basis[k] >> l) & 1:
                    basis[k] ^= w
            basis[l] = w
    for l, b in basis.items():
        if (t >> l) & 1:
            t ^= b
    if t == 0:
        return None
    q = (t & -t).bit_length() - 1
    y = 1 << q
    for l, b in basis.items():
        if (b >> q) & 1:
            y |= 1 << l
    return y


def find_alpha(t, ws):
    """alpha (mask over m) with t = XOR_{m in alpha} ws[m], or None."""
    basis = {}
    for m, w in enumerate(ws):
        c = 1 << m
        for l, (b, bc) in list(basis.items()):
            if (w >> l) & 1:
                w ^= b
                c ^= bc
        if w:
            l = (w & -w).bit_length() - 1
            for k in list(basis):
                b, bc = basis[k]
                if (b >> l) & 1:
                    basis[k] = (b ^ w, bc ^ c)
            basis[l] = (w, c)
    a = 0
    for l, (b, bc) in basis.items():
        if (t >> l) & 1:
            t ^= b
            a ^= bc
    return a if t == 0 else None


def all_witnesses(M0, Ns, R, C, side):
    """Y[z-1] for z = 1..2^sd-1 (placeholder 0 where z is killable) and the list of killable z."""
    sd, yd, c0, cN = side_vectors(M0, Ns, R, C, side)
    T0 = xor_table(c0, sd)
    TN = [xor_table(c, sd) for c in cN]
    Y, killable = [], []
    for z in range(1, 1 << sd):
        y = witness_for(T0[z], [T[z] for T in TN])
        if y is None:
            killable.append(z)
            Y.append(0)
        else:
            Y.append(y)
    return Y, killable


def killable_only(M0, Ns, R, C, side):
    return all_witnesses(M0, Ns, R, C, side)[1]


def reduce_candidate(plan, phi, lb):
    R, C, M0f, Nf = build_flat(plan, phi)
    rows, cols, M0r, Nr = reduce_matrix(M0f, Nf, R, C)
    Rr, Cr = len(rows), len(cols)
    side = 'right' if Cr <= Rr else 'left'
    sd = Cr if side == 'right' else Rr
    need = lb - plan['f']
    useful = 0 < need <= min(Rr, Cr)
    return dict(plan=plan, p=plan['p'], phi=phi, R=R, C=C, M0f=M0f, Nf=Nf, rows=rows, cols=cols, M0r=M0r, Nr=Nr,
                Rr=Rr, Cr=Cr, side=side, sd=sd, need=need, useful=useful, G=None, Y=None)


# ------------------------------------------------------------------------------------------------ path A (literal port of vw334)
def rank1_factor(Fv, m1, m2):
    p = [0] * m1
    q = [0] * m2
    first = -1
    for i in range(m1):
        for j in range(m2):
            if (Fv >> (i * m2 + j)) & 1:
                p[i] = 1
                if first < 0:
                    first = i
    if first < 0:
        raise SystemExit('zero forced slice')
    for j in range(m2):
        q[j] = (Fv >> (first * m2 + j)) & 1
    for i in range(m1):
        for j in range(m2):
            if (p[i] & q[j]) != ((Fv >> (i * m2 + j)) & 1):
                raise SystemExit('forced slice is not rank 1')
    return p, q


def pivot_positions_lists(vecs, n):
    basis, piv = [], []
    for v in vecs:
        v = list(v)
        for b in range(len(basis)):
            if v[piv[b]]:
                v = [x ^ y for x, y in zip(v, basis[b])]
        l = -1
        for i in range(n):
            if v[i]:
                l = i
                break
        if l < 0:
            continue
        for b in range(len(basis)):
            if basis[b][l]:
                basis[b] = [x ^ y for x, y in zip(basis[b], v)]
        basis.append(v)
        piv.append(l)
    return sorted(piv)


def build_dense_A(plan):
    nr, r1, m1, m2 = plan['nr'], plan['f'], plan['m1'], plan['m2']
    U = plan['U']
    Fv = [flat_slice(U[i], m2) for i in plan['Fi']]
    Rv = [flat_slice(U[i], m2) for i in plan['Ri']]
    PQ = [rank1_factor(F, m1, m2) for F in Fv]
    gb = lambda x, b: (x >> b) & 1
    D = [dict(), dict(), dict()]
    D[0]['R'], D[0]['Cc'] = nr, m1 * m2
    D[0]['m0'] = [[gb(Rv[s], b) for b in range(m1 * m2)] for s in range(nr)]
    D[1]['R'], D[1]['Cc'] = m1, nr * m2
    D[1]['m0'] = [[0] * (nr * m2) for _ in range(m1)]
    D[2]['R'], D[2]['Cc'] = m2, nr * m1
    D[2]['m0'] = [[0] * (nr * m1) for _ in range(m2)]
    for s in range(nr):
        for i in range(m1):
            for j in range(m2):
                D[1]['m0'][i][s * m2 + j] = gb(Rv[s], i * m2 + j)
                D[2]['m0'][j][s * m1 + i] = gb(Rv[s], i * m2 + j)
    for k in range(3):
        D[k]['u'], D[k]['v'] = [], []
    for s in range(nr):
        for l in range(r1):
            P, Qv = PQ[l]
            ua = [0] * nr
            ua[s] = 1
            va = [P[i] & Qv[j] for i in range(m1) for j in range(m2)]
            D[0]['u'].append(ua)
            D[0]['v'].append(va)
            ub = list(P)
            vb = [0] * (nr * m2)
            for j in range(m2):
                vb[s * m2 + j] = Qv[j]
            D[1]['u'].append(ub)
            D[1]['v'].append(vb)
            uc = list(Qv)
            vc = [0] * (nr * m1)
            for i in range(m1):
                vc[s * m1 + i] = P[i]
            D[2]['u'].append(uc)
            D[2]['v'].append(vc)
    return D


def reduce_dense_A(D):
    D['rowmap'] = list(range(D['R']))
    D['colmap'] = list(range(D['Cc']))
    for _ in range(8):
        changed = False
        cm = [list(D['m0'][r]) for r in range(D['R'])]
        for m in range(len(D['u'])):
            if any(D['u'][m][r] for r in range(D['R'])):
                cm.append(D['v'][m])
        cp = pivot_positions_lists(cm, D['Cc'])
        if len(cp) < D['Cc']:
            changed = True
            D['m0'] = [[row[c] for c in cp] for row in D['m0']]
            D['v'] = [[v[c] for c in cp] for v in D['v']]
            D['colmap'] = [D['colmap'][c] for c in cp]
            D['Cc'] = len(cp)
        rm = [[D['m0'][r][c] for r in range(D['R'])] for c in range(D['Cc'])]
        for m in range(len(D['u'])):
            if any(D['v'][m][c] for c in range(D['Cc'])):
                rm.append(D['u'][m])
        rp = pivot_positions_lists(rm, D['R'])
        if len(rp) < D['R']:
            changed = True
            D['m0'] = [D['m0'][r] for r in rp]
            D['u'] = [[u[r] for r in rp] for u in D['u']]
            D['rowmap'] = [D['rowmap'][r] for r in rp]
            D['R'] = len(rp)
        if not changed:
            break


class Aff:
    """vw334 Aff: affine system over F2, echelon by lowest set bit."""

    def __init__(self):
        self.piv = {}

    def add(self, m, r):
        while m:
            p = (m & -m).bit_length() - 1
            if p not in self.piv:
                self.piv[p] = (m, r)
                return True
            pm, pr = self.piv[p]
            m ^= pm
            r ^= pr
        return r == 0


def kprob_G_A(D, need):
    """vw334 make_kprob: killable nonzero z (bit c = reduced column/row position), right if Cc <= R else left."""
    right = D['Cc'] <= D['R']
    sd = D['Cc'] if right else D['R']
    if need <= 0 or need > min(D['R'], D['Cc']):
        return None
    rn = D['R'] if right else D['Cc']
    nm = len(D['u'])
    m0row = [0] * rn
    Urow = [0] * rn
    vv = [0] * nm
    for r in range(rn):
        for c in range(sd):
            bit = D['m0'][r][c] if right else D['m0'][c][r]
            if bit:
                m0row[r] |= 1 << c
    for m in range(nm):
        uu = D['u'][m] if right else D['v'][m]
        v2 = D['v'][m] if right else D['u'][m]
        for r in range(rn):
            if uu[r]:
                Urow[r] |= 1 << m
        for c in range(sd):
            if v2[c]:
                vv[m] |= 1 << c
    G = []
    for z in range(1, 1 << sd):
        A = Aff()
        Sz = 0
        for m in range(nm):
            if par(vv[m] & z):
                Sz |= 1 << m
        ok = True
        for r in range(rn):
            if not A.add(Sz & Urow[r], par(m0row[r] & z)):
                ok = False
                break
        if ok:
            G.append(z)
    return G


# ------------------------------------------------------------------------------------------------ certificate search
def subset_search(G, sd, need, limit=2000000):
    """All size-`need` subsets of range(sd) that contain the support of no killable vector in G (lexicographic order)."""
    valid = []
    n = 0
    for comb in itertools.combinations(range(sd), need):
        n += 1
        if n > limit:
            return valid, n - 1, True
        mask = 0
        for c in comb:
            mask |= 1 << c
        if all((g & ~mask) != 0 for g in G):
            valid.append(comb)
    return valid, n, False


def choose_positions(Fflat, m1, m2):
    f = len(Fflat)
    cols = []
    basis = {}
    for q in range(m1 * m2):
        colv = 0
        for l in range(f):
            if (Fflat[l] >> q) & 1:
                colv |= 1 << l
        w = colv
        while w:
            h = w.bit_length() - 1
            if h in basis:
                w ^= basis[h]
            else:
                basis[h] = w
                cols.append(q)
                break
        if len(cols) == f:
            break
    if len(cols) != f:
        raise SystemExit('forced slices are not independent')
    return [[q // m2, q % m2] for q in cols]


def invert_gf2(H, f):
    """G with G.H = I where (G.H)[i] = XOR_{k in G[i]} H[k] (rows are masks over j)."""
    rows = [[H[l], 1 << l] for l in range(f)]
    for col in range(f):
        piv = None
        for idx in range(col, f):
            if (rows[idx][0] >> col) & 1:
                piv = idx
                break
        if piv is None:
            raise SystemExit('H singular')
        rows[col], rows[piv] = rows[piv], rows[col]
        for idx in range(f):
            if idx != col and (rows[idx][0] >> col) & 1:
                rows[idx][0] ^= rows[col][0]
                rows[idx][1] ^= rows[col][1]
    return [rows[i][1] for i in range(f)]


def evaluate_candidates(row, verbose=False, kmax=14):
    c, lb = row['cls'], row['lb']
    pw = WANG_P[c]
    plans = {p: build_plan(row, p) for p in (0, 1, 2)}
    cands = []
    for p in [pw] + [q for q in (0, 1, 2) if q != pw]:
        for phi in 'abc':
            cand = reduce_candidate(plans[p], phi, lb)
            if cand['useful'] and cand['sd'] <= kmax:
                Y, G = all_witnesses(cand['M0r'], cand['Nr'], cand['Rr'], cand['Cr'], cand['side'])
                cand['Y'], cand['G'] = Y, G
            cands.append(cand)
    return plans, cands


def cand_line(c, cand):
    pl = cand['plan']
    K = cand['sd'] - cand['need'] if cand['useful'] else None
    kn = len(cand['G']) if cand['G'] is not None else None
    return ('row=%d p=%d phi=%s f=%d nr=%d need=%d full=%dx%d red=%dx%d side=%s sd=%d useful=%d K=%s killable=%s' % (
        c, cand['p'], cand['phi'], pl['f'], pl['nr'], cand['need'], cand['R'], cand['C'], cand['Rr'], cand['Cr'],
        cand['side'], cand['sd'], 1 if cand['useful'] else 0, K, kn))


def find_certificate(row, verbose=True):
    c, lb = row['cls'], row['lb']
    pw = WANG_P[c]
    plans, cands = evaluate_candidates(row)
    for cand in cands:
        if verbose:
            print('  cand ' + cand_line(c, cand) + (' [Wang p]' if cand['p'] == pw else ''))
    # (1) Wang orientation must reproduce the expected parameters
    krow = KPAR[c]
    wang_useful = [x for x in cands if x['p'] == pw and x['useful']]
    sig = [(x['plan']['f'], x['plan']['nr'], x['need'], x['phi'], (x['Rr'], x['Cr']), x['side'],
            (x['sd'] - x['need']) if x['useful'] else None) for x in wang_useful]
    want = (krow[3], krow[4], krow[5], krow[6], krow[7], krow[8], krow[9])
    table_match = (len(sig) == 1 and sig[0] == want)
    if verbose:
        print('  expected parameters: want %s, got %s -> %s' % (want, sig, 'MATCH' if table_match else 'MISMATCH'))
    if not table_match:
        raise SystemExit('class %d: Wang-orientation data do not reproduce the expected parameters' % c)
    # (2) direct certificates: whole reduced side, K = 0 and no killable vector
    def direct(x):
        return x['useful'] and x['G'] is not None and x['sd'] == x['need'] and not x['G']
    for x in cands:
        if direct(x):
            how = 'wang' if x['p'] == pw else 'other'
            if how == 'wang':
                choice = ('wang p=%d (%s) %dx%d %s K=0 killable=0; vw334 greedy Fi + reduce_dense rows/cols' % (
                    x['p'], x['phi'], x['Rr'], x['Cr'], x['side']))
            else:
                choice = ('other p=%d (%s) %dx%d %s K=0 killable=0; Wang p=%d has K=%d (%d killable)' % (
                    x['p'], x['phi'], x['Rr'], x['Cr'], x['side'], pw, krow[9],
                    len(next(y for y in cands if y['p'] == pw and y['useful'])['G'])))
            return finish_certificate(row, x, list(range(x['Rr'])), list(range(x['Cr'])), choice)
    # (3) subsets of the reduced side
    for x in cands:
        if not (x['useful'] and x['G'] is not None and x['sd'] > x['need']):
            continue
        valid, total, truncated = subset_search(x['G'], x['sd'], x['need'])
        if verbose:
            print('  subset search p=%d phi=%s: %d valid of %d%s (killable=%d)' % (
                x['p'], x['phi'], len(valid), total, '+' if truncated else '', len(x['G'])))
        if not valid:
            continue
        ref = HAND_SUBSET.get(c)
        if ref is not None and x['p'] == pw and tuple(ref) in valid:
            sub, why = tuple(ref), "a hand-picked subset (valid)"
        else:
            sub, why = valid[0], 'lexicographically first valid subset'
        choice = ("subset p=%d (%s) %dx%d %s K=%d (%d killable): %s = reduced positions {%s}; %d of %d size-%d subsets are "
                  "killable-free; %s" % (
                      x['p'], x['phi'], x['Rr'], x['Cr'], x['side'], x['sd'] - x['need'], len(x['G']),
                      "C'" if x['side'] == 'right' else "R'", ','.join(map(str, sub)), len(valid), total, x['need'], why))
        if x['side'] == 'right':
            return finish_certificate(row, x, list(range(x['Rr'])), list(sub), choice)
        return finish_certificate(row, x, list(sub), list(range(x['Cr'])), choice)
    raise SystemExit('class %d: no K = 0 certificate found' % c)


def finish_certificate(row, x, Rsel, Csel, choice):
    """Rsel/Csel: positions in the reduced row/column lists.  Builds all JSON fields (the row data)."""
    plan = x['plan']
    rows, cols = x['rows'], x['cols']
    Rp = [rows[r] for r in Rsel]
    Cp = [cols[c] for c in Csel]
    M0 = [pick_bits(x['M0f'][r], Cp) for r in Rp]
    N = [[pick_bits(Nm[r], Cp) for r in Rp] for Nm in x['Nf']]
    side = x['side']
    need = len(Cp) if side == 'right' else len(Rp)
    Y, killable = all_witnesses(M0, N, len(Rp), len(Cp), side)
    if killable:
        raise SystemExit('class %d: chosen R\'/C\' still has %d killable vectors' % (row['cls'], len(killable)))
    Fflat = [flat_slice(plan['U'][i], plan['m2']) for i in plan['Fi']]
    P = choose_positions(Fflat, plan['m1'], plan['m2'])
    H = [0] * plan['f']
    for l in range(plan['f']):
        for j, (u, v) in enumerate(P):
            if (plan['U'][plan['Fi'][l]][u] >> v) & 1:
                H[l] |= 1 << j
    G = invert_gf2(H, plan['f'])
    d = dict()
    d['class'] = row['cls']
    d['dim'] = len(row['basis'])
    d['lb'] = row['lb']
    d['basis'] = list(row['basis'])
    d['na'] = plan['na']
    d['pi'] = list(plan['pi'])
    d['p'] = plan['p']
    d['n0'], d['m1'], d['m2'] = plan['n0'], plan['m1'], plan['m2']
    d['U'] = [list(s) for s in plan['U']]
    d['f'] = plan['f']
    d['Fi'] = list(plan['Fi'])
    d['P'] = P
    d['G'] = G
    d['nr'] = plan['nr']
    d['Ri'] = list(plan['Ri'])
    d['phi'] = x['phi']
    d['side'] = side
    d['Rp'] = Rp
    d['Cp'] = Cp
    d['need'] = need
    d['M0'] = M0
    d['N'] = N
    d['Y'] = Y
    d['choice'] = choice
    return dict(data=d, cand=x, Rsel=Rsel, Csel=Csel)


def make_negative(cert, row):
    """Checker-level negative: claim lb+1, extend Cp (right) or Rp (left) by one index of the full flattening."""
    d = cert['data']
    x = cert['cand']
    side = d['side']
    need0 = d['need']
    Rp, Cp = list(d['Rp']), list(d['Cp'])
    R, C = x['R'], x['C']
    side2 = side
    # tier N1: extend the kernel-side list by a fresh index of the full flattening
    lst, full = (Cp, C) if side == 'right' else (Rp, R)
    unused = [i for i in range(full) if i not in lst]
    if unused:
        lst.append(unused[0])
        kind = 'N1: %s extended by fresh %s %d of the full %dx%d flattening' % (
            'Cp' if side == 'right' else 'Rp', 'column' if side == 'right' else 'row', unused[0], R, C)
    else:
        # tier N2: the side already holds every index.  Flip the form: the other side becomes the kernel side with
        # need+1 distinct indices (the positive list first, then fresh ones), the old kernel-side list is the y-space.
        if side == 'right':
            pool = Rp + [r for r in range(R) if r not in Rp]
        else:
            pool = Cp + [c for c in range(C) if c not in Cp]
        if len(pool) >= need0 + 1:
            if side == 'right':
                Rp = pool[:need0 + 1]
                side2 = 'left'
            else:
                Cp = pool[:need0 + 1]
                side2 = 'right'
            kind = 'N2: no fresh %s exists, so the form is flipped to %s with %d distinct %ss (positive list first, then fresh)' % (
                'column' if side == 'right' else 'row', side2, need0 + 1, 'row' if side == 'right' else 'column')
        else:
            # tier N3: even the flipped side has only need indices (full flattening is need x need).  Repeat the last
            # entry: the repeated column (row) makes e_last + e_new a kernel vector of M(alpha) for every alpha.
            lst.append(lst[-1])
            kind = ('N3: the full %dx%d flattening has no index left on either side, so the last entry %d of %s is '
                    'DUPLICATED (e_last+e_new is killable for every alpha)' % (
                        R, C, lst[-1], 'Cp' if side == 'right' else 'Rp'))
    need = len(Cp) if side2 == 'right' else len(Rp)
    M0 = [pick_bits(x['M0f'][r], Cp) for r in Rp]
    N = [[pick_bits(Nm[r], Cp) for r in Rp] for Nm in x['Nf']]
    neg = dict(d)
    neg['lb'] = d['lb'] + 1
    neg['side'] = side2
    neg['Rp'], neg['Cp'], neg['need'] = Rp, Cp, need
    neg['M0'], neg['N'] = M0, N
    neg['Y'] = []
    neg['choice'] = 'NEG lb+1=%d, need=%d (K-L holds), Y empty, emitter refuses; %s' % (d['lb'] + 1, need, kind)
    return neg


# ------------------------------------------------------------------------------------------------ independent self-checks
_T3 = None


def t3():
    global _T3
    if _T3 is None:
        _T3 = [[[0] * 12 for _ in range(12)] for _ in range(9)]
        for a in range(9):
            for b in range(12):
                for c in range(12):
                    n = 0
                    for i in range(3):
                        for j in range(3):
                            for k in range(4):
                                if a == 3 * i + j and b == 4 * j + k and c == 3 * k + i:
                                    n ^= 1
                    _T3[a][b][c] = n
    return _T3


def full_dims(phi, nr, m1, m2):
    if phi == 'a':
        return nr, m1 * m2
    if phi == 'b':
        return m1, nr * m2
    return m2, nr * m1


def phi_idx(phi, r, c, m1, m2):
    """Flattening: entry (row r, column c) of flattening phi is V[s][u][v] for the returned (s, u, v)."""
    if phi == 'a':
        u, v = divmod(c, m2)
        return r, u, v
    if phi == 'b':
        s, v = divmod(c, m2)
        return s, r, v
    s, u = divmod(c, m1)
    return s, u, r


def chk_fields(d):
    keys = ['class', 'dim', 'lb', 'basis', 'na', 'pi', 'p', 'n0', 'm1', 'm2', 'U', 'f', 'Fi', 'P', 'G', 'nr', 'Ri', 'phi',
            'side', 'Rp', 'Cp', 'need', 'M0', 'N', 'Y', 'choice']
    if list(d.keys()) != keys:
        return False, 'field list/order differs: %s' % list(d.keys())
    return True, '26 fields'


def chk_pi(d):
    basis, pi, na = d['basis'], d['pi'], d['na']
    if len(basis) != d['dim'] or rank_masks(basis) != len(basis):
        return False, 'basis dependent or dim wrong'
    if na != 9 - len(basis) or len(pi) != na:
        return False, 'na/pi length'
    for b in basis:
        if not 0 < b < 512:
            return False, 'basis mask out of range'
        for x in range(na):
            if par(pi[x] & b):
                return False, 'pi(basis %d)_%d = 1' % (b, x)
    for x in range(na):
        if not 0 <= pi[x] < 512:
            return False, 'pi mask out of range'
    if rank_masks(pi) != na:
        return False, 'pi has rank %d < na = %d (not onto, so ker pi would be larger than S)' % (rank_masks(pi), na)
    return True, '%d basis masks in ker pi; pi onto F2^%d, so ker pi = S exactly' % (len(basis), na)


def chk_u(d):
    T = t3()
    na, pi, p = d['na'], d['pi'], d['p']
    if p == 0:
        n0, m1, m2 = na, 12, 12
    elif p == 1:
        n0, m1, m2 = 12, 12, na
    elif p == 2:
        n0, m1, m2 = 12, na, 12
    else:
        return False, 'bad p'
    if (d['n0'], d['m1'], d['m2']) != (n0, m1, m2):
        return False, 'n0/m1/m2 differ from the mode order'
    Q = [[[0] * 12 for _ in range(12)] for _ in range(na)]
    for x in range(na):
        for b in range(12):
            for c in range(12):
                s = 0
                for a in range(9):
                    if (pi[x] >> a) & 1:
                        s ^= T[a][b][c]
                Q[x][b][c] = s
    U = d['U']
    if len(U) != n0:
        return False, 'len(U)'
    for i in range(n0):
        if len(U[i]) != m1:
            return False, 'slice %d has %d rows' % (i, len(U[i]))
        for u in range(m1):
            if U[i][u] >> m2:
                return False, 'U[%d][%d] has bits >= m2' % (i, u)
            for v in range(m2):
                if p == 0:
                    e = Q[i][u][v]
                elif p == 1:
                    e = Q[v][i][u]
                else:
                    e = Q[u][v][i]
                if ((U[i][u] >> v) & 1) != e:
                    return False, 'U[%d][%d][%d] differs from T334/pi/p' % (i, u, v)
    return True, 'U = U^(p=%d) from T334 and pi, %d x %d x %d' % (p, n0, m1, m2)


def chk_f1(d):
    U, Fi, P, G, f = d['U'], d['Fi'], d['P'], d['G'], d['f']
    if len(Fi) != f or len(P) != f or len(G) != f or len(set(Fi)) != f:
        return False, 'lengths / Fi not injective'
    for i in Fi:
        if not 0 <= i < d['n0']:
            return False, 'Fi out of range'
    for u, v in P:
        if not (0 <= u < d['m1'] and 0 <= v < d['m2']):
            return False, 'P out of range'
    H = [[(U[Fi[l]][P[j][0]] >> P[j][1]) & 1 for j in range(f)] for l in range(f)]
    for i in range(f):
        if G[i] >> f:
            return False, 'G row too wide'
        for j in range(f):
            s = 0
            for k in range(f):
                s ^= ((G[i] >> k) & 1) & H[k][j]
            if s != (1 if i == j else 0):
                return False, '(G.H)[%d][%d] = %d' % (i, j, s)
    return True, 'G.H = I (f=%d), Fi injective' % f


def chk_ri(d):
    U, Fi, Ri = d['U'], d['Fi'], d['Ri']
    nonzero = [i for i in range(d['n0']) if any(U[i])]
    expect = [i for i in nonzero if i not in Fi]
    if Ri != expect:
        return False, 'Ri = %s but the other nonzero slices are %s' % (Ri, expect)
    if set(Fi) & set(Ri):
        return False, 'Fi and Ri overlap'
    if d['nr'] != len(Ri):
        return False, 'nr != len(Ri)'
    return True, 'Ri = every other nonzero slice (%d), Fi/Ri disjoint' % len(Ri)


def chk_m(d, rng, nsamp=40, allow_dup=False):
    U, Fi, Ri, f, nr, m1, m2, phi = d['U'], d['Fi'], d['Ri'], d['f'], d['nr'], d['m1'], d['m2'], d['phi']
    Rp, Cp, M0, N = d['Rp'], d['Cp'], d['M0'], d['N']
    R, C = full_dims(phi, nr, m1, m2)
    if not allow_dup and (len(set(Rp)) != len(Rp) or len(set(Cp)) != len(Cp)):
        return False, 'repeated index in Rp/Cp'
    if any(not 0 <= r < R for r in Rp) or any(not 0 <= c < C for c in Cp):
        return False, 'Rp/Cp out of the full %dx%d flattening' % (R, C)
    if len(M0) != len(Rp) or len(N) != nr * f:
        return False, 'M0 / N sizes'
    for r in range(len(Rp)):
        if M0[r] >> len(Cp):
            return False, 'M0 row too wide'
        for j in range(len(Cp)):
            s, u, v = phi_idx(phi, Rp[r], Cp[j], m1, m2)
            if ((M0[r] >> j) & 1) != ((U[Ri[s]][u] >> v) & 1):
                return False, 'M0[%d][%d] differs from phi(U\'(0))' % (r, j)
    for s0 in range(nr):
        for l in range(f):
            Nm = N[s0 * f + l]
            if len(Nm) != len(Rp):
                return False, 'N matrix size'
            for r in range(len(Rp)):
                if Nm[r] >> len(Cp):
                    return False, 'N row too wide'
                for j in range(len(Cp)):
                    s, u, v = phi_idx(phi, Rp[r], Cp[j], m1, m2)
                    e = ((U[Fi[l]][u] >> v) & 1) if s == s0 else 0
                    if ((Nm[r] >> j) & 1) != e:
                        return False, 'N[%d][%d][%d] differs from phi(E_{%d,%d})' % (s0 * f + l, r, j, s0, l)
    # linearity (L-K4): phi(U'(alpha)) restricted equals M0 + sum alpha_m N_m, alpha random
    for _ in range(nsamp):
        alpha = [[rng.randrange(2) for _ in range(f)] for _ in range(nr)]
        for r in range(len(Rp)):
            for j in range(len(Cp)):
                s, u, v = phi_idx(phi, Rp[r], Cp[j], m1, m2)
                e = (U[Ri[s]][u] >> v) & 1
                for l in range(f):
                    if alpha[s][l]:
                        e ^= (U[Fi[l]][u] >> v) & 1
                g = (M0[r] >> j) & 1
                for s0 in range(nr):
                    for l in range(f):
                        if alpha[s0][l]:
                            g ^= (N[s0 * f + l][r] >> j) & 1
                if e != g:
                    return False, 'affine identity fails at (%d,%d)' % (r, j)
    return True, 'M0/N = restriction of phi(U\'(0)), phi(E_sl) by definition; affine identity on %d random alpha' % nsamp


def chk_l(d):
    f, need, lb = d['f'], d['need'], d['lb']
    side_len = len(d['Cp']) if d['side'] == 'right' else len(d['Rp'])
    if need != side_len:
        return False, 'need != |side|'
    if f + need < lb:
        return False, 'f + need = %d < lb = %d' % (f + need, lb)
    return True, 'f + need = %d + %d = %d >= lb %d%s' % (f, need, f + need, lb, '' if f + need == lb else ' (strict)')


def chk_w(d):
    M0, N, Y, side = d['M0'], d['N'], d['Y'], d['side']
    nR, nC = len(d['Rp']), len(d['Cp'])
    sd = nC if side == 'right' else nR
    yd = nR if side == 'right' else nC
    if d['need'] != sd:
        return False, 'need != |side|'
    if len(Y) != (1 << sd) - 1:
        return False, 'len(Y) = %d, want %d' % (len(Y), (1 << sd) - 1)
    for z in range(1, 1 << sd):
        y = Y[z - 1]
        if y < 0 or y >> yd:
            return False, 'Y[%d] out of range' % (z - 1)
        if side == 'right':
            t = 0
            for r in range(nR):
                if par(M0[r] & z):
                    t |= 1 << r
        else:
            t = 0
            for r in range(nR):
                if (z >> r) & 1:
                    t ^= M0[r]
        if par(y & t) != 1:
            return False, 'witness fails y.M0 z = 1 at z=%d' % z
        for m, Nm in enumerate(N):
            if side == 'right':
                w = 0
                for r in range(nR):
                    if par(Nm[r] & z):
                        w |= 1 << r
            else:
                w = 0
                for r in range(nR):
                    if (z >> r) & 1:
                        w ^= Nm[r]
            if par(y & w) != 0:
                return False, 'witness fails y.N_%d z = 0 at z=%d' % (m, z)
    return True, 'all %d witnesses satisfy y.M0 z = 1 and y.N_m z = 0 (%d matrices)' % ((1 << sd) - 1, len(N))


def chk_deep(d, rng, nsamp=3000):
    """Not a kernel fact: sample (or enumerate, nr*f <= 16) alpha and test rank M(alpha)[Rp,Cp] >= need."""
    M0, N, need = d['M0'], d['N'], d['need']
    nm = len(N)
    nR = len(d['Rp'])
    if nm <= 16:
        cur = list(M0)
        mn = rank_masks(cur)
        gray = 0
        for t in range(1, 1 << nm):
            g = (t & -t).bit_length() - 1
            for r in range(nR):
                cur[r] ^= N[g][r]
            gray ^= 1 << g
            rk = rank_masks(cur)
            if rk < mn:
                mn = rk
        if mn < need:
            return False, 'exhaustive: min rank %d < need %d' % (mn, need)
        return True, 'EXHAUSTIVE over all 2^%d alpha: min rank M(alpha)[Rp,Cp] = %d >= need %d' % (nm, mn, need)
    mn = 10 ** 9
    for _ in range(nsamp):
        a = rng.getrandbits(nm)
        cur = list(M0)
        for m in range(nm):
            if (a >> m) & 1:
                for r in range(nR):
                    cur[r] ^= N[m][r]
        mn = min(mn, rank_masks(cur))
    if mn < need:
        return False, 'sampled: min rank %d < need %d' % (mn, need)
    return True, 'sampled %d random alpha (not a proof): min rank = %d >= need %d' % (nsamp, mn, need)


def check_data(d, seed=1, deep=True, allow_dup=False):
    rng = random.Random(seed + d['class'])
    res = []
    for name, fn in (('fields', chk_fields), ('K-pi', chk_pi), ('K-U', chk_u), ('K-F1', chk_f1), ('Ri/Fi', chk_ri)):
        try:
            res.append((name,) + fn(d))
        except Exception as e:  # report instead of crash
            res.append((name, False, 'exception %r' % (e,)))
    for name, fn in (('K-M', lambda dd: chk_m(dd, rng, allow_dup=allow_dup)), ('K-L', chk_l), ('K-W', chk_w)):
        try:
            res.append((name,) + fn(d))
        except Exception as e:
            res.append((name, False, 'exception %r' % (e,)))
    if deep:
        try:
            res.append(('deep-alpha',) + chk_deep(d, rng))
        except Exception as e:
            res.append(('deep-alpha', False, 'exception %r' % (e,)))
    return res


# ------------------------------------------------------------------------------------------------ negative refusal
def refuse_negative(neg, tag):
    """Try to build the witness table of the lb+1 claim from the negative's own data.  Must fail; prints the refusal."""
    M0, N, side = neg['M0'], neg['N'], neg['side']
    nR, nC = len(neg['Rp']), len(neg['Cp'])
    Y, killable = all_witnesses(M0, N, nR, nC, side)
    sd = nC if side == 'right' else nR
    if not killable:
        print('NOT REFUSED %s: every z has a witness -- the lb+1 claim would be certified (BUG or genuine)' % tag)
        return False
    z = killable[0]
    sdim, yd, c0, cN = side_vectors(M0, N, nR, nC, side)

    def vec_at(cols):
        v = 0
        for j in range(sdim):
            if (z >> j) & 1:
                v ^= cols[j]
        return v

    alpha = find_alpha(vec_at(c0), [vec_at(c) for c in cN])
    if alpha is None:
        print('INTERNAL ERROR %s: z=%d reported killable but no alpha found' % (tag, z))
        return False
    # verify M(alpha) z = 0 on the restricted matrices
    Ma = list(M0)
    for m in range(len(N)):
        if (alpha >> m) & 1:
            for r in range(nR):
                Ma[r] ^= N[m][r]
    if side == 'right':
        bad = [r for r in range(nR) if par(Ma[r] & z)]
    else:
        acc = 0
        for r in range(nR):
            if (z >> r) & 1:
                acc ^= Ma[r]
        bad = [c for c in range(nC) if (acc >> c) & 1]
    ok_alpha = (not bad)
    print('REFUSED %s: claim lb=%d needs a witness for each of the %d nonzero z, but %d of them have none; first z=%d (0x%x): '
          'M0 z lies in span{N_m z}; alpha=0x%x gives M(alpha) z = 0 (%s)' % (
              tag, neg['lb'], (1 << sd) - 1, len(killable), z, z, alpha, 'verified on M0/N' if ok_alpha else 'NOT VERIFIED'))
    return ok_alpha


# ------------------------------------------------------------------------------------------------ output helpers
def dumps(d):
    parts = []
    for k, v in d.items():
        parts.append('  %s: %s' % (json.dumps(k), json.dumps(v, separators=(',', ':'))))
    return '{\n' + ',\n'.join(parts) + '\n}\n'


def write_json(path, d):
    with open(path, 'w') as fh:
        fh.write(dumps(d))


def read_json(path):
    with open(path) as fh:
        return json.load(fh)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        h.update(fh.read())
    return h.hexdigest()


# ------------------------------------------------------------------------------------------------ modes
def cmd_explore(classes):
    rows = load_rows(classes)
    for c in classes:
        row = rows[c]
        print('EXPLORE class %d dim %d lb %d basis %s (Wang p=%d)' % (c, row['dim'], row['lb'], row['basis'], WANG_P[c]))
        plans, cands = evaluate_candidates(row)
        for x in cands:
            print('  ' + cand_line(c, x) + (' [Wang p]' if x['p'] == WANG_P[c] else ''))
        # path A (literal vw334 port) vs path B at Wang's p
        pw = WANG_P[c]
        plan = plans[pw]
        D = build_dense_A(plan)
        for k, phi in enumerate('abc'):
            reduce_dense_A(D[k])
            xb = next(y for y in cands if y['p'] == pw and y['phi'] == phi)
            same_rc = (D[k]['rowmap'] == xb['rows'] and D[k]['colmap'] == xb['cols'])
            need = row['lb'] - plan['f']
            GA = kprob_G_A(D[k], need) if (0 < need <= min(D[k]['R'], D[k]['Cc']) and min(D[k]['R'], D[k]['Cc']) <= 14) else None
            same_g = (GA == xb['G']) if (GA is not None and xb['G'] is not None) else None
            print('  pathA-vs-pathB p=%d phi=%s: reduced %dx%d rows/cols equal=%s killable(A)=%s killable(B)=%s equal=%s' % (
                pw, phi, D[k]['R'], D[k]['Cc'], same_rc, None if GA is None else len(GA),
                None if xb['G'] is None else len(xb['G']), same_g))
            if not same_rc or same_g is False:
                print('  *** PATH A / PATH B MISMATCH class %d phi %s' % (c, phi))
        krow = KPAR[c]
        wang_useful = [x for x in cands if x['p'] == pw and x['useful']]
        sig = [(x['plan']['f'], x['plan']['nr'], x['need'], x['phi'], (x['Rr'], x['Cr']), x['side'], x['sd'] - x['need'])
               for x in wang_useful]
        want = (krow[3], krow[4], krow[5], krow[6], krow[7], krow[8], krow[9])
        print('  expected parameters %s -> %s' % (want, 'MATCH' if sig == [want] else 'MISMATCH got %s' % sig))
        sys.stdout.flush()


def plan_with_F(base, Fi_list):
    """Same slices, other forced set Fi_list (must meet K-F1); Ri = every other nonzero slice."""
    U = base['U']
    Ri = [i for i in range(base['n0']) if any(U[i]) and i not in Fi_list]
    plan = dict(base)
    plan['Fi'], plan['Ri'], plan['f'], plan['nr'] = list(Fi_list), Ri, len(Fi_list), len(Ri)
    return plan


def cmd_explore_fi(classes, maxextra=3):
    """Informational: enlarge the forced set by independent non-rank-1 slices (K-F1 is the only hypothesis of L-K2)."""
    rows = load_rows(classes)
    for c in classes:
        row = rows[c]
        print('EXPLORE_FI class %d lb %d' % (c, row['lb']))
        for p in (1, 2):
            base = build_plan(row, p)
            U, m2 = base['U'], base['m2']
            extras = base['Ri']
            for k in range(0, min(maxextra, len(extras)) + 1):
                for E in itertools.combinations(extras, k):
                    Fl = list(base['Fi']) + list(E)
                    if rank_masks([flat_slice(U[i], m2) for i in Fl]) != len(Fl):
                        continue
                    plan = plan_with_F(base, Fl)
                    if plan['nr'] == 0:
                        continue
                    for phi in 'abc':
                        cand = reduce_candidate(plan, phi, row['lb'])
                        if not cand['useful']:
                            continue
                        kn = None
                        if cand['sd'] <= 14:
                            kn = len(killable_only(cand['M0r'], cand['Nr'], cand['Rr'], cand['Cr'], cand['side']))
                        print('  p=%d extraF=%s f=%d nr=%d phi=%s need=%d red=%dx%d side=%s sd=%d K=%d killable=%s%s' % (
                            p, list(E), plan['f'], plan['nr'], phi, cand['need'], cand['Rr'], cand['Cr'], cand['side'],
                            cand['sd'], cand['sd'] - cand['need'], kn,
                            '   <== DIRECT K=0' if (kn == 0 and cand['sd'] == cand['need']) else ''))
        sys.stdout.flush()


def cmd_emit(outdir, classes):
    rows = load_rows(classes)
    allok = True
    print('python', sys.version.replace('\n', ' '))
    for c in classes:
        row = rows[c]
        print('=== class %d (dim %d, lb %d, basis %s)' % (c, row['dim'], row['lb'], row['basis']))
        cert = find_certificate(row)
        d = cert['data']
        path = '%s/row%d.json' % (outdir, c)
        write_json(path, d)
        d2 = read_json(path)
        assert d2 == d, 'JSON round trip differs'
        res = check_data(d2)
        bad = [r for r in res if not r[1]]
        for name, ok, detail in res:
            print('  CHECK %-10s %s  %s' % (name, 'OK  ' if ok else 'FAIL', detail))
        if bad:
            allok = False
        # path A at the chosen (p, phi): reduced rows/cols and killable set must equal path B's
        x = cert['cand']
        D = build_dense_A(x['plan'])
        k = 'abc'.index(x['phi'])
        reduce_dense_A(D[k])
        okrc = (D[k]['rowmap'] == x['rows'] and D[k]['colmap'] == x['cols'])
        GA = kprob_G_A(D[k], x['need']) if x['sd'] <= 14 else None
        okg = (GA == x['G']) if GA is not None else None
        print('  CHECK pathA==pathB  %s  reduced rows/cols equal=%s, killable sets equal=%s (%s killable)' % (
            'OK  ' if okrc and okg is not False else 'FAIL', okrc, okg, None if GA is None else len(GA)))
        if not okrc or okg is False:
            allok = False
        # negative
        neg = make_negative(cert, row)
        negpath = '%s/row%d_neg.json' % (outdir, c)
        write_json(negpath, neg)
        neg2 = read_json(negpath)
        assert neg2 == neg
        print('  NEG ' + neg2['choice'])
        negres = [r for r in check_data(neg2, deep=False, allow_dup=True) if r[0] not in ('K-W',)]
        negbad = [r for r in negres if not r[1]]
        print('  NEG data checks (all but K-W): %s' % ('OK' if not negbad else 'FAIL %s' % negbad))
        kw = chk_w(neg2)
        print('  NEG K-W (Y empty): %s %s' % ('REJECTED' if not kw[0] else 'ACCEPTED(!)', kw[1]))
        refused = refuse_negative(neg2, 'row%d_neg' % c)
        if negbad or kw[0] or not refused:
            allok = False
        print('  sha256 row%d.json %s  row%d_neg.json %s' % (c, sha256_file(path), c, sha256_file(negpath)))
        sys.stdout.flush()
    print('ALL_OK' if allok else 'SOME_FAILED')
    return 0 if allok else 1


def cmd_check(outdir, classes):
    allok = True
    for c in classes:
        d = read_json('%s/row%d.json' % (outdir, c))
        res = check_data(d)
        for name, ok, detail in res:
            print('row %d CHECK %-10s %s  %s' % (c, name, 'OK  ' if ok else 'FAIL', detail))
            allok = allok and ok
        neg = read_json('%s/row%d_neg.json' % (outdir, c))
        refused = refuse_negative(neg, 'row%d_neg' % c)
        kw = chk_w(neg)
        allok = allok and refused and not kw[0]
    print('ALL_OK' if allok else 'SOME_FAILED')
    return 0 if allok else 1


def cmd_summary(outdir):
    lines = ['class\tp\tf\tnr\tphi\tside\tneed\t|Rp|\t|Cp|\tchoice']
    for c in CLASSES:
        path = '%s/row%d.json' % (outdir, c)
        if not os.path.exists(path):
            continue
        d = read_json(path)
        lines.append('%d\t%d\t%d\t%d\t%s\t%s\t%d\t%d\t%d\t%s' % (
            d['class'], d['p'], d['f'], d['nr'], d['phi'], d['side'], d['need'], len(d['Rp']), len(d['Cp']), d['choice']))
    with open(outdir + '/summary.tsv', 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
    return 0


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__ if __doc__ else 'usage: explore|emit|check|summary')
    mode = argv[1]
    if mode == 'explore':
        cmd_explore([int(x) for x in argv[2:]] or CLASSES)
        return 0
    if mode == 'explore_fi':
        cmd_explore_fi([int(x) for x in argv[2:]] or [54, 65])
        return 0
    if mode == 'emit':
        return cmd_emit(argv[2], [int(x) for x in argv[3:]] or CLASSES)
    if mode == 'check':
        return cmd_check(argv[2], [int(x) for x in argv[3:]] or CLASSES)
    if mode == 'summary':
        return cmd_summary(argv[2])
    raise SystemExit('unknown mode ' + mode)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
