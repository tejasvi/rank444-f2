#!/usr/bin/env python3
"""s16_row44.py OUT_JSON : the data of row 44's coset-count certificate.
s16_row44.py OUT_JSON certs : add the per-mask certificates (list 'certs') to OUT_JSON.
s16_row44.py OUT_JSON lean OUT_DIR : write the Lean modules Row44Certs.lean (data) and Row44C0..7.lean (chunk facts)
  into OUT_DIR (= lean/B334/Bind).
The first form reads the seeded table: --table FILE (default seeded334.tsv in the current directory).

S = span(basis of class 44) has codimension 3, so 7 nonzero cosets c (representative: the smallest mask of the coset).
For each c, S_c = span(basis + [c]) is a G0-image of a table class: a witness g = (P, Q) in GL3 x GL3 with
g(span(B_class)) = S_c, found by search over all 168 x 168 elements and the classes of dimension 7.  The JSON carries,
per coset: c, the class, its lb and basis, P, Q and their inverses (9-bit masks, entry (i, j) at bit 3i + j), the masks of
g(b) for b in B_class, and the masks of g^-1(x) for x in basis + [c] (the two halves of the span equality).
"""
import json
import sys

TAB = 'seeded334.tsv'
if '--table' in sys.argv:   # the seeded table (default: seeded334.tsv in the current directory)
    _i = sys.argv.index('--table'); TAB = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]


def mat(m):
    return [[(m >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)]


def unmat(A):
    return sum(A[i][j] << (3 * i + j) for i in range(3) for j in range(3))


def mul(A, B):
    return [[sum(A[i][k] & B[k][j] for k in range(3)) & 1 for j in range(3)] for i in range(3)]


def act(P, Q, v):
    return unmat(mul(mul(P, mat(v)), Q))


def rref(vs):
    piv = {}
    for b in vs:
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
    return tuple(sorted(piv.values()))


def in_span(vs, m):
    return rref(list(vs) + [m]) == rref(vs)


def main():
    rows = {}
    for line in open(TAB):
        f = line.rstrip('\n').split('\t')
        if f[0] != 'idx':
            rows[int(f[0])] = f
    basis = [int(x) for x in rows[44][2].split(',')]
    lb44 = int(rows[44][11])
    S = rref(basis)
    reps, seen = [], set()
    for m in range(1, 512):
        if in_span(basis, m):
            continue
        key = rref(basis + [m])
        if key in seen:
            continue
        seen.add(key)
        reps.append(m)
    assert len(reps) == 7, reps
    # GL3: the 3x3 matrices whose 3 rows (3-bit masks) are independent
    GL = [m for m in range(512) if len(rref([(m >> (3 * i)) & 7 for i in range(3)])) == 3]
    assert len(GL) == 168, len(GL)
    inv = {}
    for m in GL:
        for n in GL:
            if unmat(mul(mat(m), mat(n))) == unmat([[1, 0, 0], [0, 1, 0], [0, 0, 1]]):
                inv[m] = n
                break
    cand = [c for c, f in rows.items() if f[1] == '7']
    out = {'class': 44, 'lb': lb44, 'basis': basis, 'cosets': []}
    for c in reps:
        Sc = rref(basis + [c])
        found = None
        for k in sorted(cand):
            Bk = [int(x) for x in rows[k][2].split(',')]
            for Pm in GL:
                P = mat(Pm)
                for Qm in GL:
                    Q = mat(Qm)
                    img = [act(P, Q, b) for b in Bk]
                    if rref(img) == Sc:
                        found = (k, Bk, Pm, Qm, img)
                        break
                if found:
                    break
            if found:
                break
        assert found, 'coset %d: no class' % c
        k, Bk, Pm, Qm, img = found
        Pi, Qi = inv[Pm], inv[Qm]
        invimg = [act(mat(Pi), mat(Qi), x) for x in basis + [c]]
        assert all(in_span(Bk, m) for m in invimg)
        out['cosets'].append({'c': c, 'class': k, 'lb': int(rows[k][11]), 'cbasis': Bk, 'P': Pm, 'Q': Qm, 'Pi': Pi,
                              'Qi': Qi, 'img': img, 'invimg': invimg})
        print('coset %d -> class %d (lb %s) via P=%d Q=%d' % (c, k, rows[k][11], Pm, Qm))
    tot = sum(x['lb'] for x in out['cosets'])
    print('sum of lb = %d; 6 * (lb44 - 1) = %d; bound holds: %s' % (tot, 6 * (lb44 - 1), tot > 6 * (lb44 - 1)))
    json.dump(out, open(sys.argv[1], 'w'), indent=1)


if __name__ == '__main__' and len(sys.argv) == 2:   # the search; the modes 'certs' and 'lean' below do not rerun it
    main()


def certs(out_json):
    """per-mask certificates for 'every vector outside S lies in exactly one S_c': for m in S a subset of the basis
    with XOR m; for m outside S the coset index i0, a subset of basis + [c_i0] with XOR m, and for every other j a
    dual vector y with y . b = 0 for b in basis + [c_j] and y . m = 1 (so m is not in that span)."""
    D = json.load(open(out_json))
    basis = D['basis']
    cl = [basis + [x['c']] for x in D['cosets']]

    def subset(B, m):
        for s in range(1 << len(B)):
            v = 0
            for i, b in enumerate(B):
                if (s >> i) & 1:
                    v ^= b
            if v == m:
                return s
        return None

    def par(x):
        return bin(x).count('1') & 1
    res = []
    for m in range(512):
        s = subset(basis, m)
        if s is not None:
            res.append([0, 0, s, [0] * 7])
            continue
        i0 = [i for i in range(7) if subset(cl[i], m) is not None]
        assert len(i0) == 1, (m, i0)
        i0 = i0[0]
        duals = []
        for j in range(7):
            if j == i0:
                duals.append(0)
                continue
            y = next(y for y in range(1, 512) if all(par(y & b) == 0 for b in cl[j]) and par(y & m) == 1)
            duals.append(y)
        res.append([1, i0, subset(cl[i0], m), duals])
    D['certs'] = res
    json.dump(D, open(out_json, 'w'), indent=None)
    print('certs: %d masks, %d inside S, %d outside' % (len(res), sum(1 for r in res if r[0] == 0), sum(1 for r in res if r[0] == 1)))


if __name__ == '__main__' and len(sys.argv) > 2 and sys.argv[2] == 'certs':
    certs(sys.argv[1])


def lean_certs(out_json, out_dir):
    """OUT_JSON as Lean modules in OUT_DIR (= .../B334/Bind): the data module Row44Certs.lean (basis, cosets, the 512
    certificates in 8 chunks of 64 masks; core Lean only, no imports) and the chunk facts Row44C<k>.lean (k = 0..7), one
    `decide +kernel` fact per chunk (the kernel's memory grows with the work: a probe measured about 5 MB per mask over
    the 6.4 GB import baseline, so 64 masks per module stay far under 8 GB)."""
    import hashlib
    import os
    raw = open(out_json, 'rb').read()
    D = json.loads(raw)
    h = hashlib.sha256(raw).hexdigest()[:16]
    C = D['certs']
    assert len(C) == 512
    ents = ['(%d, %d, %d, [%s])' % (kind, i0, s, ', '.join(str(y) for y in duals) if kind == 1 else '')
            for kind, i0, s, duals in C]
    L = ['/-! # Row 44: data of the coset-count certificate. GENERATED by a script from',
         'its data; do not edit.',
         '',
         '`basis` spans S (class 44); `cs` lists the coset representatives c; `ClN i` generates S_c for c = `cs[i]`.',
         '`certs<k>` holds the certificates of the masks 64k … 64k + 63: entry m is (kind, i0, subset, duals). Kind 0: m is in',
         'S, the XOR of the basis elements selected by `subset`. Kind 1: m is in S_{i0}, the XOR of the elements of `ClN i0`',
         'selected by `subset`, and for every j ≠ i0 the mask duals[j] has even overlap with every element of `ClN j` and odd',
         'overlap with m (so m is not in S_j). -/',
         '',
         'namespace B334.Row44', '',
         'def basis : List Nat := [%s]' % ', '.join(str(b) for b in D['basis']),
         'def cs : List Nat := [%s]' % ', '.join(str(x['c']) for x in D['cosets']),
         'def ClN (i : Nat) : List Nat := basis ++ [cs.getD i 0]', '']
    for k in range(8):
        L += ['def certs%d : List (Nat × Nat × Nat × List Nat) := [' % k]
        L += ['  ' + e + (',' if i < 63 else '') for i, e in enumerate(ents[64 * k:64 * k + 64])]
        L += [']', '']
    L += ['def certsK (k : Nat) : List (Nat × Nat × Nat × List Nat) :=',
          '  ' + ' '.join('if k = %d then certs%d else' % (k, k) for k in range(7)) + ' certs7', '',
          'end B334.Row44']
    open(os.path.join(out_dir, 'Row44Certs.lean'), 'w').write('\n'.join(L) + '\n')
    for k in range(8):
        M = ['import B334.Bind.Rows', 'import B334.Bind.Row44Certs', '',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
             '/-! # Row 44: certificate check of the masks %d … %d. GENERATED by a script; do not edit. -/' % (64 * k, 64 * k + 63),
             '', 'namespace B334.Row44', 'open B334.Bind', '',
             'theorem hc%d : chkAll (fun c m => chkC basis ClN 7 c m) certs%d (64 * %d) = true := by decide +kernel' % (k, k, k),
             '', 'end B334.Row44']
        open(os.path.join(out_dir, 'Row44C%d.lean' % k), 'w').write('\n'.join(M) + '\n')
    print('lean certs: 512 entries in 8 chunks -> %s/Row44Certs.lean, Row44C0..7.lean (json sha %s)' % (out_dir, h))


if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[2] == 'lean':
    lean_certs(sys.argv[1], sys.argv[3])
