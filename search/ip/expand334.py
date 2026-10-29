#!/usr/bin/env python3
"""Step 2a: all subspaces S' of A = F2^9 that contain a point P, with their <3,3,4> class (Wang's 710 orbit classes under
G0 = {a -> P a Q}), found by expanding every class representative over G0.  For each P (classes 706/707/708: rank 1/2/3)
writes sup_P<cls>.npz with, for every strict superspace S' != P: its dim, class, the nonzero cosets of S'/P in the
coordinates of L_P (quotient map of quotinstc), and the inverse incidence (coset -> superspaces).
Checks: the number of distinct S' containing P must be 417,199 (= number of subspaces of F2^8), and every S' must get a
single class.
usage: expand334.py [--data DIR]   (reads DIR/seeded334.npz, writes DIR/sup_P706.npz, sup_P707.npz, sup_P708.npz)
"""
import sys, time
import numpy as np
from numba import njit
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common334 import build_img0, quotient_map, RANK9

DATA = "./"
if "--data" in sys.argv:   # directory of seeded334.npz and sup_P<cls>.npz (default: the current directory)
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
t0 = time.time()
z = np.load(DATA + "seeded334.npz")
bases, dims, n123 = z["bases"].astype(np.int64), z["dims"].astype(np.int64), z["n123"]
img = build_img0()
G = img.shape[0]
PTS = [(706, 1), (707, 10), (708, 84)]


@njit(cache=False)
def rref(rows, d):
    r = 0
    for bit in range(8, -1, -1):
        piv = -1
        for i in range(r, d):
            if (rows[i] >> bit) & 1:
                piv = i
                break
        if piv < 0:
            continue
        t = rows[r]; rows[r] = rows[piv]; rows[piv] = t
        for i in range(d):
            if i != r and (rows[i] >> bit) & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


@njit(cache=False)
def in_span(rows, d, v):
    for i in range(d):
        p = 8
        while not ((rows[i] >> p) & 1):
            p -= 1
        if (v >> p) & 1:
            v ^= rows[i]
    return v == 0


@njit(cache=False)
def expand(img, bases, dims, P, nout):
    hi = np.empty(nout, np.uint64); lo = np.empty(nout, np.uint64); cl = np.empty(nout, np.int16)
    rows = np.empty(9, np.int64)
    k = 0
    for c in range(bases.shape[0]):
        d = dims[c]
        if d == 0:
            continue
        for g in range(img.shape[0]):
            for i in range(d):
                rows[i] = img[g, bases[c, i]]
            rref(rows, d)
            if in_span(rows, d, P):
                h = np.uint64(0); l = np.uint64(0)
                for i in range(d):
                    sh = 9 * i
                    v = np.uint64(rows[i])
                    if sh + 9 <= 64:
                        l |= v << np.uint64(sh)
                    elif sh >= 64:
                        h |= v << np.uint64(sh - 64)
                    else:
                        l |= v << np.uint64(sh)
                        h |= v >> np.uint64(64 - sh)
                hi[k] = h; lo[k] = l; cl[k] = c
                k += 1
    return hi[:k], lo[:k], cl[:k], k


@njit(cache=False)
def build_cosets(keys_lo, keys_hi, sdims, LP):
    """members of S'/P (nonzero cosets as 8-bit vectors) for every superspace (CSR)."""
    n = len(sdims)
    indptr = np.zeros(n + 1, np.int64)
    for s in range(n):
        indptr[s + 1] = indptr[s] + (1 << (sdims[s] - 1)) - 1
    mem = np.empty(indptr[n], np.int16)
    rows = np.empty(9, np.int64); bas = np.empty(9, np.int64)
    for s in range(n):
        d = sdims[s]
        for i in range(d):
            sh = 9 * i
            if sh + 9 <= 64:
                rows[i] = (keys_lo[s] >> np.uint64(sh)) & np.uint64(511)
            elif sh >= 64:
                rows[i] = (keys_hi[s] >> np.uint64(sh - 64)) & np.uint64(511)
            else:
                rows[i] = ((keys_lo[s] >> np.uint64(sh)) | (keys_hi[s] << np.uint64(64 - sh))) & np.uint64(511)
        nb = 0
        for i in range(d):          # independent images under L_P
            v = LP[rows[i]]
            for j in range(nb):
                p = 7
                while not ((bas[j] >> p) & 1):
                    p -= 1
                if (v >> p) & 1:
                    v ^= bas[j]
            if v:
                p = 7
                while not ((v >> p) & 1):
                    p -= 1
                # keep bas in echelon with distinct pivots
                for j in range(nb):
                    if (bas[j] >> p) & 1:
                        bas[j] ^= v
                bas[nb] = v
                nb += 1
        if nb != d - 1:
            return indptr, mem, s
        # enumerate span (nonzero)
        base = indptr[s]
        cnt = 0
        for m in range(1, 1 << nb):
            v = 0
            for j in range(nb):
                if (m >> j) & 1:
                    v ^= bas[j]
            mem[base + cnt] = v
            cnt += 1
    return indptr, mem, -1


for cls, P in PTS:
    r = RANK9[P]
    Nr = int((RANK9 == r).sum())
    nout = int(sum(G * int(n123[c, r - 1]) // Nr for c in range(len(dims)) if dims[c] > 0))
    hi, lo, cl, k = expand(img, bases, dims, P, nout)
    assert k == nout, (k, nout)
    order = np.lexsort((lo, hi))
    hi, lo, cl = hi[order], lo[order], cl[order]
    newk = np.ones(len(hi), bool)
    newk[1:] = (hi[1:] != hi[:-1]) | (lo[1:] != lo[:-1])
    grp = np.cumsum(newk) - 1
    # class consistency: all entries of one key share the class
    first_cl = cl[newk]
    incons = int((cl != first_cl[grp]).sum())
    hi, lo, cl = hi[newk], lo[newk], first_cl
    sd = dims[cl]
    nsub = len(hi)
    print(f"P class {cls} (rank {r}, vec {P}): images {k}, distinct superspaces {nsub}, class inconsistencies {incons}, "
          f"by dim {np.bincount(sd, minlength=10).tolist()}  ({time.time()-t0:.1f}s)")
    assert nsub == 417199 and incons == 0
    L, D = quotient_map([P])
    LP = np.array([L(v) for v in range(512)], dtype=np.int64)
    keep = sd >= 2                       # strict superspaces (drop S' = P)
    hi, lo, cl, sd = hi[keep], lo[keep], cl[keep], sd[keep]
    indptr, mem, bad = build_cosets(lo, hi, sd, LP)
    assert bad == -1, bad
    nco = np.bincount(mem, minlength=256)
    assert nco[0] == 0 and (nco[1:] == nco[1]).all(), "every coset must lie in the same number of superspaces"
    # inverse incidence coset -> superspaces
    sup_of = np.repeat(np.arange(len(sd)), np.diff(indptr))
    o2 = np.argsort(mem, kind="stable")
    inc = sup_of[o2].astype(np.int32)
    incptr = np.zeros(257, np.int64)
    incptr[1:] = np.cumsum(nco)
    np.savez(DATA + f"sup_P{cls}.npz", P=P, D=D, LP=LP, cls=cl, dims=sd, hi=hi, lo=lo, mptr=indptr, mem=mem,
             incptr=incptr, inc=inc)
    print(f"  strict superspaces {len(sd)}, coset incidences {len(mem)}, each coset in {nco[1]} superspaces; saved "
          f"({time.time()-t0:.1f}s)")
print(f"done in {time.time()-t0:.1f}s")
