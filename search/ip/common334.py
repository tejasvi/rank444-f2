"""Shared functions of the instance programs (seed334.py, expand334.py, mkip334.py, mkipS.py, mkcompS.py).

Conventions (Wang, problems/matrix/tensor.h): <N0,N1,N2> has T[i*N1+j][j*N2+k][k*N0+i] = 1.
First factors / constraint vectors: 9-bit masks, bit 3i+j = entry (i,j) of the 3x3 first argument.
Wang's certificate entry = a subspace S of A (basis = 'constraints') and lb = lower bound for R(T mod S).
"""
import codecs, re
import numpy as np



def parse_cert(path):
    txt = open(path, encoding="latin-1").read()
    out = []
    for b in txt.split("constrained_tensors {")[1:]:
        m = re.search(r'constraints: "((?:[^"\\]|\\.)*)"', b)
        vecs = []
        if m:
            raw = codecs.escape_decode(m.group(1).encode("latin-1"))[0]
            assert len(raw) % 2 == 0
            vecs = [raw[i] | (raw[i + 1] << 8) for i in range(0, len(raw), 2)]
        lb = int(re.search(r"rank_lower_bound: (\d+)", b).group(1))
        kind = re.search(r"rank_lower_bound_proof \{\s*([a-z_]+)", b)
        idx = re.search(r"^\s*index: (\d+)", b, re.M)
        out.append(dict(index=int(idx.group(1)) if idx else 0, vecs=vecs, lb=lb, kind=kind.group(1) if kind else "?"))
    for i, e in enumerate(out):
        assert e["index"] == i, (path, i, e["index"])
    return out


def rank_f2_list(rows):
    rows = [int(r) for r in rows if r]
    rk = 0
    while rows:
        piv = rows.pop()
        rk += 1
        hb = piv.bit_length() - 1
        rows = [r ^ piv if (r >> hb) & 1 else r for r in rows]
        rows = [r for r in rows if r]
    return rk


def mat_rank9(v):
    return rank_f2_list([(v >> (3 * i)) & 7 for i in range(3)])


RANK9 = np.array([mat_rank9(v) for v in range(512)], dtype=np.int8)
TR9 = np.array([sum(((v >> (3 * i + j)) & 1) << (3 * j + i) for i in range(3) for j in range(3)) for v in range(512)],
               dtype=np.uint16)


def span_list(vecs):
    s = [0]
    for v in vecs:
        if v not in s:
            s = s + [x ^ v for x in s]
    return s


def gl3_mats():
    out = []
    for bits in range(512):
        M = np.array([(bits >> k) & 1 for k in range(9)], dtype=np.int64).reshape(3, 3)
        d = (M[0, 0] * (M[1, 1] * M[2, 2] + M[1, 2] * M[2, 1]) + M[0, 1] * (M[1, 0] * M[2, 2] + M[1, 2] * M[2, 0])
             + M[0, 2] * (M[1, 0] * M[2, 1] + M[1, 1] * M[2, 0])) % 2
        if d:
            out.append(M)
    assert len(out) == 168
    return out


def build_img0():
    """img0[g, v] = mask of P @ mat(v) @ Q over F2, g = p*168 + q (the group G0 = GL3 x GL3 acting a -> P a Q)."""
    G = np.array(gl3_mats(), dtype=np.int64)
    Ms = np.array([np.array([(v >> k) & 1 for k in range(9)]).reshape(3, 3) for v in range(512)], dtype=np.int64)
    w = (1 << np.arange(9)).astype(np.int64)
    img = np.zeros((168 * 168, 512), dtype=np.uint16)
    for p in range(168):
        PB = np.einsum('ab,vbc->vac', G[p], Ms)
        R = np.einsum('vac,qcd->qvad', PB, G) % 2          # (168, 512, 3, 3)
        img[p * 168:(p + 1) * 168] = (R.reshape(168, 512, 9) * w).sum(-1).astype(np.uint16)
    return img


def tensor334():
    T = np.zeros((9, 12, 12), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(4):
                T[3 * i + j, 4 * j + k, 3 * k + i] = 1
    return T


def tensor333():
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * k + i] = 1
    return T


def quotient_map(Svecs, n=9):
    """L: F2^n -> F2^(n-d) with kernel span(Svecs) (reduced echelon basis; non-pivot bits compressed), as quotinstc."""
    basis = []
    for v in Svecs:
        for p, b in basis:
            if (v >> p) & 1:
                v ^= b
        if v:
            p = v.bit_length() - 1
            basis = [(pp, bb ^ v if (bb >> p) & 1 else bb) for pp, bb in basis]
            basis.append((p, v))
    piv = {p for p, _ in basis}
    comp = [x for x in range(n) if x not in piv]

    def L(a):
        for p, b in basis:
            if (a >> p) & 1:
                a ^= b
        r = 0
        for i, c in enumerate(comp):
            if (a >> c) & 1:
                r |= 1 << i
        return r
    return L, len(comp)


def rank_f2_matrix(M):
    """rank over F2 of a 0/1 numpy matrix (rows packed as python ints)."""
    rows = [int("".join(str(int(x)) for x in r[::-1]), 2) if r.any() else 0 for r in M]
    return rank_f2_list(rows)


def flattening_ranks(T, Svecs):
    """ranks of the three flattenings of T mod span(Svecs)."""
    L, D = quotient_map(Svecs, T.shape[0])
    Tq = np.zeros((D,) + T.shape[1:], dtype=np.uint8)
    for x in range(T.shape[0]):
        lx = L(1 << x)
        for xp in range(D):
            if (lx >> xp) & 1:
                Tq[xp] ^= T[x]
    ra = rank_f2_matrix(Tq.reshape(D, -1)) if D else 0
    rb = rank_f2_matrix(Tq.transpose(1, 0, 2).reshape(T.shape[1], -1)) if D else 0
    rc = rank_f2_matrix(Tq.transpose(2, 0, 1).reshape(T.shape[2], -1)) if D else 0
    return ra, rb, rc
