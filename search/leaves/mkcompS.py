#!/usr/bin/env python3
"""Completion inputs for quotient raises: for each class, T mod S (S = the class representative) as a tsolve334 target in the
reduced coordinates of quotient_map(S basis) (lines 'x y z', as mkinst334.write_target), the leaves of its capacity search as
instances ('leaf<k>: c1 .. cL', c = coset coordinates of the 9-bit labels), and a positive control: the rank-29 scheme moved
by the g in G0 that puts the most first factors into S, its other first factors mod S (completion must be SAT).
usage: mkcompS.py OUTDIR LEAFDIR CLASS... --scheme SCHEME.exp [--data DIR]   (leaves LEAFDIR/leaves_c<CLASS>.txt; writes
  OUTDIR/qS_c<CLASS>.t, pos_c<CLASS>.a, inst_c<CLASS>.a; reads DIR/seeded334.npz; SCHEME.exp: a rank-29 scheme of <3,3,4>)
"""
import re, sys
import numpy as np
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ip"))
from common334 import quotient_map, tensor334, build_img0

DATA = "./"
if "--data" in sys.argv:   # directory of seeded334.npz and sup_P<cls>.npz (default: the current directory)
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
_i = sys.argv.index("--scheme"); SCHEME = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
out, leafdir = sys.argv[1], sys.argv[2]
z = np.load(DATA + "seeded334.npz")
img = build_img0().astype(np.int64)
T = tensor334()


def fm(expr, var, idx):
    m = 0; expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        expr = expr[1:-1]
    for sign, coef, r, cc in re.findall(r"([+-]?)\s*(?:(\d+)\*)?" + var + r"(\d)(\d)", expr):
        if (int(coef) if coef else 1) % 2:
            m ^= 1 << idx(int(r) - 1, int(cc) - 1)
    return m


firsts = []
for ln in open(SCHEME):
    ln = ln.strip()
    if not ln:
        continue
    parts, d, cur = [], 0, ""
    for ch in ln:
        d += (ch == "(") - (ch == ")")
        if ch == "*" and d == 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    parts.append(cur)
    a = fm(parts[0], "a", lambda i, j: 3 * i + j); b = fm(parts[1], "b", lambda j, k: 4 * j + k)
    cc = fm(parts[2], "c", lambda k, i: 3 * k + i)
    if a and b and cc:
        firsts.append(a)
assert len(firsts) == 29

for c in [int(x) for x in sys.argv[3:]]:
    dS = int(z["dims"][c]); Sb = [int(v) for v in z["bases"][c][:dS]]
    L, D = quotient_map(Sb)
    LT = [L(1 << x) for x in range(9)]
    Tp = {}
    for x in range(9):
        for y in range(12):
            for zz in range(12):
                if T[x, y, zz]:
                    for xp in range(D):
                        if (LT[x] >> xp) & 1:
                            Tp[(xp, y, zz)] = Tp.get((xp, y, zz), 0) ^ 1
    with open(f"{out}/qS_c{c}.t", "w") as f:
        for (x, y, zz), v in sorted(Tp.items()):
            if v:
                f.write(f"{x} {y} {zz}\n")
    memS = np.zeros(512, bool); span = [0]
    for v in Sb:
        span = span + [x ^ v for x in span]
    memS[span] = True
    cnt = memS[img[:, firsts]].sum(axis=1)
    g = int(np.argmax(cnt))
    prof = sorted(L(int(img[g, a])) for a in firsts if not memS[img[g, a]])
    with open(f"{out}/pos_c{c}.a", "w") as f:
        f.write(f"pos{len(prof)}_c{c}: " + " ".join(map(str, prof)) + "\n")
    n = 0
    with open(f"{out}/inst_c{c}.a", "w") as f:
        for ln in open(f"{leafdir}/leaves_c{c}.txt"):
            v = [int(x) for x in ln.split()]
            if not v:
                continue
            n += 1
            f.write(f"leaf{n}: " + " ".join(str(L(a)) for a in sorted(v)) + "\n")
    print(f"class {c} (dim {dS}, D={D}): target {sum(1 for v in Tp.values() if v)} entries; positive control {len(prof)} "
          f"first factors ({int(cnt[g])} of 29 moved into S); {n} leaf instances")
