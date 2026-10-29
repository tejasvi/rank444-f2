#!/usr/bin/env python3
"""Coset-profile IP for <3,3,4> mod S, S = the representative of a G0-class of dimension dS >= 2 (lines, planes), in the
format of lineenum9vr: 'R <L> N <ncos>', the coset labels (smallest 9-bit representative of each nonzero coset of A/S),
one row 'C <dim S''> <cap> <size> <labels>' per strict superspace S'' of S (cap = L - lb(S''), seeded table), and
'G <|Stab(S)|>' with the induced label permutations.  A profile of length L survives iff it meets every cap; if none
survives (and no leaf completes), R(T mod S) >= L + 1.
Superspaces are found as in expand334.py: every class representative of larger dimension is moved by every g in G0 and
kept when its span contains S.  Checks: the number of distinct strict superspaces equals the number of nonzero subspaces
of A/S, each gets one class, and every coset lies in the same number of superspaces.
usage: mkipS.py CLASS L OUT_IP [OUT_SUMMARY] [--data DIR]   (reads DIR/seeded334.npz)
"""
import sys, time
import numpy as np
from numba import njit
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common334 import build_img0, quotient_map

DATA = "./"
if "--data" in sys.argv:   # directory of seeded334.npz and sup_P<cls>.npz (default: the current directory)
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
t0 = time.time()
cS, L, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
z = np.load(DATA + "seeded334.npz")
bases, dims, seeded = z["bases"].astype(np.int64), z["dims"].astype(np.int64), z["seeded"].astype(np.int64)
dS = int(dims[cS]); Sb = [int(v) for v in bases[cS][:dS]]
memS = np.zeros(512, np.bool_)
span = [0]
for v in Sb:
    span = span + [x ^ v for x in span]
memS[span] = True
img = build_img0().astype(np.int64)
G = img.shape[0]


@njit(cache=False)
def rref(rows, d):
    r = 0
    for bit in range(8, -1, -1):
        piv = -1
        for i in range(r, d):
            if (rows[i] >> bit) & 1:
                piv = i; break
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
def expand(img, bases, dims, Sb, dS, fill, hi, lo, cl):
    rows = np.empty(9, np.int64); k = 0
    for c in range(bases.shape[0]):
        d = dims[c]
        if d <= dS:
            continue
        for g in range(img.shape[0]):
            for i in range(d):
                rows[i] = img[g, bases[c, i]]
            rref(rows, d)
            ok = True
            for j in range(dS):
                if not in_span(rows, d, Sb[j]):
                    ok = False; break
            if ok:
                if fill:
                    h = np.uint64(0); l = np.uint64(0)
                    for i in range(d):
                        sh = 9 * i; v = np.uint64(rows[i])
                        if sh + 9 <= 64:
                            l |= v << np.uint64(sh)
                        elif sh >= 64:
                            h |= v << np.uint64(sh - 64)
                        else:
                            l |= v << np.uint64(sh); h |= v >> np.uint64(64 - sh)
                    hi[k] = h; lo[k] = l; cl[k] = c
                k += 1
    return k


Sbn = np.array(Sb, np.int64)
dummy = np.zeros(1, np.uint64)
n = expand(img, bases, dims, Sbn, dS, False, dummy, dummy, np.zeros(1, np.int16))
hi = np.empty(n, np.uint64); lo = np.empty(n, np.uint64); cl = np.empty(n, np.int16)
expand(img, bases, dims, Sbn, dS, True, hi, lo, cl)
order = np.lexsort((lo, hi)); hi, lo, cl = hi[order], lo[order], cl[order]
newk = np.ones(len(hi), bool); newk[1:] = (hi[1:] != hi[:-1]) | (lo[1:] != lo[:-1])
grp = np.cumsum(newk) - 1; first = cl[newk]
incons = int((cl != first[grp]).sum())
hi, lo, cl = hi[newk], lo[newk], first.astype(np.int64)
cod = 9 - dS
# number of nonzero subspaces of F2^cod (all dims 1..cod)
def gauss(n_, k_):
    num = 1; den = 1
    for i in range(k_):
        num *= (2 ** (n_ - i) - 1); den *= (2 ** (i + 1) - 1)
    return num // den
expect = sum(gauss(cod, k) for k in range(1, cod + 1))
print(f"class {cS}: dim {dS}, basis {Sb}, seeded lb {seeded[cS]}; images {n}, distinct strict superspaces {len(hi)} "
      f"(expected {expect}), class inconsistencies {incons} ({time.time()-t0:.1f}s)")
assert len(hi) == expect and incons == 0
Lq, D = quotient_map(Sb)
LS = np.array([Lq(v) for v in range(512)], np.int64)
ncos = (1 << D) - 1
rep = np.zeros(ncos + 1, np.int64)
for v in range(511, 0, -1):
    if LS[v]:
        rep[LS[v]] = v
assert (rep[1:] > 0).all()
rowsets = []
for s in range(len(hi)):
    d = int(dims[cl[s]]); vec = []
    for i in range(d):
        sh = 9 * i
        if sh + 9 <= 64:
            v = (int(lo[s]) >> sh) & 511
        elif sh >= 64:
            v = (int(hi[s]) >> (sh - 64)) & 511
        else:
            v = ((int(lo[s]) >> sh) | (int(hi[s]) << (64 - sh))) & 511
        vec.append(v)
    imgs = set([0])
    for v in vec:
        imgs = imgs | {x ^ int(LS[v]) for x in imgs}
    mem = sorted(x for x in imgs if x)
    assert len(mem) == (1 << (d - dS)) - 1, (s, d, len(mem))
    rowsets.append((d, int(cl[s]), mem))
cnt = np.zeros(ncos + 1, np.int64)
for d, c, mem in rowsets:
    for x in mem:
        cnt[x] += 1
assert cnt[0] == 0 and (cnt[1:] == cnt[1]).all()
stab = [g for g in range(G) if memS[img[g, Sbn]].all()]
perms = [[int(LS[img[g, rep[l + 1]]]) - 1 for l in range(ncos)] for g in stab]
assert all(min(p) >= 0 and len(set(p)) == ncos for p in perms)
rowsets.sort(key=lambda t: (t[0], t[1], t[2]))
caps = [L - int(seeded[c]) for d, c, mem in rowsets]
if min(caps) < 0:
    print(f"MONOTONE: a strict superspace has lb {L - min(caps)} > L = {L}, so R(T mod S) > L already (no IP written)")
    sys.exit(3)
with open(out, "w") as f:
    f.write(f"R {L} N {ncos}\n" + " ".join(str(int(v)) for v in rep[1:]) + "\n")
    for (d, c, mem), cap in zip(rowsets, caps):
        f.write(f"C {d} {cap} {len(mem)} " + " ".join(str(x - 1) for x in mem) + "\n")
    f.write(f"G {len(stab)}\n")
    for p in perms:
        f.write(" ".join(map(str, p)) + "\n")
single = [cap for (d, c, mem), cap in zip(rowsets, caps) if len(mem) == 1]
summ = (f"class {cS} (dim {dS}, lb {seeded[cS]}) at L={L}: {ncos} cosets, {len(rowsets)} rows, |Stab|={len(stab)}; "
        f"label caps (superspaces one dim up) min {min(single)} max {max(single)} hist {np.bincount(single).tolist()}; "
        f"rows by dim {np.bincount([d for d, c, mem in rowsets]).tolist()}")
print(summ)
if len(sys.argv) > 4:
    open(sys.argv[4], "a").write(summ + "\n")
print(f"wrote {out} ({time.time()-t0:.1f}s)")
