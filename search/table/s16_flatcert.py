#!/usr/bin/env python3
"""s16_flatcert.py OUT_DIR [CLASSES] [--table FILE] : method-K certificates with f = 0 (plain flattening bounds) for the table rows whose
seeded value equals a flattening rank of T mod S (forced products with no forced slices; same JSON format as
emit_k.py's).  Default classes: every 'flatten_matrix_proof' row plus the forced-product rows 5, 11, 15, 32 (seeded = flat).

For a row: p = 0 (U = Q, the quotient by pi), Fi = [], Ri = every nonzero slice, and the flattening (a), (b) or (c)
with rank >= lb.  Rp, Cp: an lb x lb invertible submatrix (pivot rows and columns of a Gaussian elimination), right
form; Y[z] = e_r for the first row r where M0' z is nonzero (no N matrices, so this is a witness).
"""
import json
import os
import sys

TAB = 'seeded334.tsv'
if '--table' in sys.argv:   # the seeded table (default: seeded334.tsv in the current directory)
    _i = sys.argv.index('--table'); TAB = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]


def T334(a, b, c):
    i, j = divmod(a, 3)
    j2, k = divmod(b, 4)
    k2, i2 = divmod(c, 3)
    return 1 if (j == j2 and k == k2 and i == i2) else 0


def reducer(B):
    piv = {}
    for b in sorted(B, key=lambda x: x.bit_length()):
        v = b
        for p in sorted(piv, reverse=True):
            if (v >> p) & 1:
                v ^= piv[p]
        if v:
            p = v.bit_length() - 1
            for q in list(piv):
                if (piv[q] >> p) & 1:
                    piv[q] ^= v
            piv[p] = v
    return piv


def rank_and_pivots(rows, ncols):
    """rows: list of int masks over ncols; returns (pivot row indices, pivot columns) of a full elimination"""
    basis = []  # (mask, pivot col, original row index set as combination not needed)
    prow, pcol = [], []
    work = []
    for ri, r in enumerate(rows):
        v = r
        for (m, pc) in work:
            if (v >> pc) & 1:
                v ^= m
        if v:
            pc = (v & -v).bit_length() - 1
            work.append((v, pc))
            prow.append(ri)
            pcol.append(pc)
    return prow, pcol


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=False)
    rows = {}
    for line in open(TAB):
        f = line.rstrip('\n').split('\t')
        if f[0] == 'idx':
            continue
        rows[int(f[0])] = f
    if len(sys.argv) > 2:
        classes = [int(x) for x in sys.argv[2].split(',')]
    else:
        classes = sorted(c for c, f in rows.items() if f[7] == 'flatten_matrix_proof') + [5, 11, 15, 32]
    summ = []
    for c in classes:
        f = rows[c]
        B = [int(x) for x in f[2].split(',')] if f[2] else []
        lb = int(f[11])
        piv = reducer(B)
        np_ = [x for x in range(9) if x not in piv]
        na = len(np_)

        def red(a):
            v = a
            for p in sorted(piv, reverse=True):
                if (v >> p) & 1:
                    v ^= piv[p]
            return v
        # pi rows: pi[x] bit a = bit np[x] of red(e_a)
        pi = [sum(((red(1 << a) >> np_[x]) & 1) << a for a in range(9)) for x in range(na)]
        assert all((sum(((pi[x] >> a) & 1) * ((b >> a) & 1) for a in range(9)) % 2) == 0 for x in range(na) for b in B)
        Q = [[[sum(((pi[x] >> a) & 1) * T334(a, y, z) for a in range(9)) % 2 for z in range(12)] for y in range(12)]
             for x in range(na)]
        # p = 0: U = Q (n0 = na, m1 = 12, m2 = 12); slices = x
        U = [[sum(Q[x][y][z] << z for z in range(12)) for y in range(12)] for x in range(na)]
        Ri = [x for x in range(na) if any(U[x])]
        nr = len(Ri)
        V = [[[Q[Ri[s]][y][z] for z in range(12)] for y in range(12)] for s in range(nr)]
        best = None
        for phi in 'abc':
            if phi == 'a':
                R = nr; Cn = 144
                mat = [sum(V[s][u][v] << (u * 12 + v) for u in range(12) for v in range(12)) for s in range(nr)]
            elif phi == 'b':
                R = 12; Cn = nr * 12
                mat = [sum(V[s][u][v] << (s * 12 + v) for s in range(nr) for v in range(12)) for u in range(12)]
            else:
                R = 12; Cn = nr * 12
                mat = [sum(V[s][u][v] << (s * 12 + u) for s in range(nr) for u in range(12)) for v in range(12)]
            prow, pcol = rank_and_pivots(mat, Cn)
            if len(prow) >= lb and best is None:
                best = (phi, mat, prow[:lb], pcol[:lb])
        assert best is not None, 'class %d: no flattening reaches lb %d' % (c, lb)
        phi, mat, prow, pcol = best
        # the lb x lb submatrix on the first lb pivot rows/cols is invertible? (pivots of the elimination give an
        # invertible submatrix on the chosen rows and pivot columns); verify by rank
        sub = [sum(((mat[r] >> cc) & 1) << j for j, cc in enumerate(pcol)) for r in prow]
        assert len(rank_and_pivots(sub, lb)[0]) == lb, 'class %d: submatrix singular' % c
        Rp, Cp = prow, pcol
        M0 = sub
        Y = []
        for z in range(1, 1 << lb):
            w = [bin(M0[r] & z).count('1') & 1 for r in range(lb)]
            r0 = w.index(1)
            Y.append(1 << r0)
        J = {'class': c, 'dim': int(f[1]), 'lb': lb, 'basis': B, 'na': na, 'pi': pi, 'p': 0, 'n0': na, 'm1': 12, 'm2': 12,
             'U': U, 'f': 0, 'Fi': [], 'P': [], 'G': [], 'nr': nr, 'Ri': Ri, 'phi': phi, 'side': 'right', 'Rp': Rp,
             'Cp': Cp, 'need': lb, 'M0': M0, 'N': [], 'Y': Y,
             'choice': 'flattening (f = 0): p=0 phi=%s, %dx%d invertible submatrix from elimination pivots' % (phi, lb, lb)}
        json.dump(J, open(os.path.join(out, 'row%d.json' % c), 'w'))
        summ.append('%d\tlb=%d\tna=%d\tnr=%d\tphi=%s' % (c, lb, na, nr, phi))
    open(os.path.join(out, 'summary.tsv'), 'w').write('\n'.join(summ) + '\n')
    print('\n'.join(summ))


if __name__ == '__main__':
    main()
