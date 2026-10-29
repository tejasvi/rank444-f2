#!/usr/bin/env python3
"""The seeded 710-class table for <3,3,4> (seeded334.tsv, seeded334.npz) and the symmetrized LP.

usage: seed334.py WANG_CERTS RANK333 OUTDIR
  WANG_CERTS  the directory certs/matrix of Wang's repository (cert_matrix_q02_n333.pb.txt, cert_matrix_q02_n334.pb.txt)
  RANK333     the unpacked rank333-f2 release (lean/HC/RRTable.lean, data/classes/routes.tsv)
  OUTDIR      where seeded334.tsv and seeded334.npz are written

- G0 = {a -> P a Q} (GL3 x GL3) is the A-slot group of <3,3,4>; G0 plus transposition is the A-slot group of <3,3,3>.
- Validations: (V1) Wang's 496 <3,3,3> reps pairwise inequivalent under G0+tr; (V2) Wang's 710 <3,3,4> reps pairwise
  inequivalent under G0; (V3) every <3,3,4> rep lies in exactly one <3,3,3> class; (V4) flattening ranks of T mod S
  (our tensor convention) never exceed Wang's bound and equal it for the classes Wang settles by a flattening.
- final333 = max(Wang333, Rudich-Rousseau table, 3x3-paper raises (routes.tsv), class 492 -> 21, class 495 -> 23).
- gain g(S) = 3 - min(dim L_row(S), dim L_col(S)); seeded334(S) = max(Wang334(S), final333(class(S)) + g(S)).
- LP: weights w1,w2,w3 per point of rank 1/2/3 (49/294/168 points); sum = r; for every class S:
  n1(S) w1 + n2(S) w2 + n3(S) w3 <= r - lb(S); type: 49 w1 + 588 w2 + 504 w3 >= 36 (split flattening, sum rk >= 36).
"""
import re, sys, time
from collections import defaultdict
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common334 import (parse_cert, RANK9, TR9, span_list, build_img0, tensor333, tensor334,
                       flattening_ranks)

t0 = time.time()
CERT333 = os.path.join(sys.argv[1], "cert_matrix_q02_n333.pb.txt")
CERT334 = os.path.join(sys.argv[1], "cert_matrix_q02_n334.pb.txt")
RRTABLE = os.path.join(sys.argv[2], "lean", "HC", "RRTable.lean")
ROUTES = os.path.join(sys.argv[2], "data", "classes", "routes.tsv")
DATA = sys.argv[3].rstrip("/") + "/"
c333 = parse_cert(CERT333)
c334 = parse_cert(CERT334)
print(f"parsed: 333 classes {len(c333)}, 334 classes {len(c334)}")


def invariants(vecs):
    sp = span_list(vecs)
    h = [0, 0, 0, 0]
    for v in sp:
        h[RANK9[v]] += 1
    return (len(vecs), h[1], h[2], h[3]), sp


for e in c333 + c334:
    e["inv"], e["span"] = invariants(e["vecs"])
    m = np.zeros(512, dtype=bool)
    m[e["span"]] = True
    e["mem"] = m

img = build_img0()
print(f"img0 built {img.shape} in {time.time()-t0:.1f}s")
assert np.all(np.sort(img, axis=1) == np.arange(512)[None, :]), "each g must permute F2^9"


def equiv(S, R, allow_tr):
    """exists g in G0 (or G0 o tr if allow_tr) with g(S) = R (S and R of the same dimension)."""
    if len(S["vecs"]) == 0:
        return True
    for basis in ([S["vecs"]] + ([[int(TR9[v]) for v in S["vecs"]]] if allow_tr else [])):
        ok = np.ones(img.shape[0], dtype=bool)
        for v in basis:
            ok &= R["mem"][img[:, v]]
            if not ok.any():
                break
        if ok.any():
            return True
    return False


# V1, V2: pairwise inequivalence within invariant groups
for name, cl, tr in (("333", c333, True), ("334", c334, False)):
    groups = defaultdict(list)
    for e in cl:
        groups[e["inv"]].append(e)
    npairs = bad = 0
    for g in groups.values():
        for a in range(len(g)):
            for b in range(a + 1, len(g)):
                npairs += 1
                if equiv(g[a], g[b], tr):
                    bad += 1
                    print(f"  V-FAIL {name}: classes {g[a]['index']} and {g[b]['index']} equivalent")
    print(f"V{'1' if name=='333' else '2'} {name}: {len(groups)} invariant groups, {npairs} pairs tested, equivalent pairs {bad}")

# V3: map each 334 class to its 333 class
g333 = defaultdict(list)
for e in c333:
    g333[e["inv"]].append(e)
cmap = np.full(len(c334), -1, dtype=np.int32)
nmulti = 0
for e in c334:
    hits = [r["index"] for r in g333[e["inv"]] if equiv(e, r, True)]
    if len(hits) != 1:
        nmulti += 1
        print(f"  V3-FAIL 334 class {e['index']}: hits {hits}")
    else:
        cmap[e["index"]] = hits[0]
cnt = np.bincount(cmap[cmap >= 0], minlength=len(c333))
print(f"V3: 334->333 map failures {nmulti}; 333 classes hit once {int((cnt==1).sum())}, twice {int((cnt==2).sum())}, "
      f"other {int(((cnt!=1)&(cnt!=2)).sum())}")

# V4: flattening consistency
for name, cl, T in (("333", c333, tensor333()), ("334", c334, tensor334())):
    over = eq_flat = nflat = 0
    for e in cl:
        fr = flattening_ranks(T, e["vecs"])
        e["flat"] = max(fr)
        if e["flat"] > e["lb"]:
            over += 1
            print(f"  V4-FAIL {name} class {e['index']}: flattening {fr} > Wang lb {e['lb']}")
        if e["kind"] == "flatten_matrix_proof":
            nflat += 1
            eq_flat += int(e["flat"] == e["lb"])
    print(f"V4 {name}: classes with flattening > Wang lb: {over}; flatten-proof classes {nflat}, equal {eq_flat}")

# final 333 table
rr = {}
for line in open(RRTABLE):
    if line.startswith("theorem al_row_"):
        for c, lb in re.findall(r"\((\d+), (\d+)\)", line):
            rr[int(c)] = max(rr.get(int(c), 0), int(lb))
routes = {}
for line in open(ROUTES):
    if line.startswith("#") or not line.strip():
        continue
    f = line.split("\t")
    routes[int(f[0])] = int(f[1])
extra = {492: 21, 495: 23}
final333 = np.zeros(len(c333), dtype=np.int32)
for e in c333:
    c = e["index"]
    final333[c] = max(e["lb"], rr.get(c, 0), routes.get(c, 0), extra.get(c, 0))
print(f"RR entries {len(rr)} (missing {len(c333)-len(rr)}), routes {len(routes)}; final>Wang333 for "
      f"{int((final333 > np.array([e['lb'] for e in c333])).sum())} classes; final[495]={final333[495]}, "
      f"points {final333[492]},{final333[493]},{final333[494]}")


def lam_dims(sp):
    s = set(sp)
    rowd = sum(1 for lam in range(1, 8) if all((lam << (3 * i)) in s for i in range(3)))
    cold = sum(1 for mu in range(1, 8) if all(sum(((mu >> i) & 1) << (3 * i + j) for i in range(3)) in s for j in range(3)))
    return int(np.log2(rowd + 1)), int(np.log2(cold + 1))


wang334 = np.array([e["lb"] for e in c334], dtype=np.int32)
gain = np.zeros(len(c334), dtype=np.int32)
seeded = np.zeros(len(c334), dtype=np.int32)
for e in c334:
    dr, dc = lam_dims(e["span"])
    g = 3 - min(dr, dc)
    gain[e["index"]] = g
    seeded[e["index"]] = max(e["lb"], final333[cmap[e["index"]]] + g)
dims = np.array([e["inv"][0] for e in c334])
print("seeded vs Wang334 by dim S: (classes, raised, max raise)")
for d in range(10):
    sel = dims == d
    if sel.any():
        diff = seeded[sel] - wang334[sel]
        print(f"  dim {d}: {int(sel.sum())} classes, raised {int((diff>0).sum())}, max raise {int(diff.max())}, "
              f"Wang range {wang334[sel].min()}-{wang334[sel].max()}, seeded range {seeded[sel].min()}-{seeded[sel].max()}")
pts = [e["index"] for e in c334 if e["inv"][0] == 1]
for p in pts:
    print(f"  point class {p}: rank {RANK9[c334[p]['vecs'][0]]}, Wang {wang334[p]}, 333-class {cmap[p]} final333 "
          f"{final333[cmap[p]]}, gain {gain[p]}, seeded {seeded[p]}")
print(f"  full tensor (class {len(c334)-1}): Wang {wang334[-1]}, seeded {seeded[-1]}")

n123 = np.array([e["inv"][1:] for e in c334], dtype=np.int64)
with open(DATA + "seeded334.tsv", "w") as f:
    f.write("idx\tdim\tbasis\tn1\tn2\tn3\twang334\tkind\tcls333\tfinal333\tgain\tseeded\tflat\n")
    for e in c334:
        i = e["index"]
        f.write(f"{i}\t{e['inv'][0]}\t{','.join(map(str, e['vecs']))}\t{n123[i,0]}\t{n123[i,1]}\t{n123[i,2]}\t"
                f"{wang334[i]}\t{e['kind']}\t{cmap[i]}\t{final333[cmap[i]]}\t{gain[i]}\t{seeded[i]}\t{e['flat']}\n")
np.savez(DATA + "seeded334.npz", wang334=wang334, seeded=seeded, gain=gain, cmap=cmap, final333=final333, n123=n123,
         dims=dims, bases=np.array([e["vecs"] + [0] * (9 - len(e["vecs"])) for e in c334], dtype=np.int32))

# symmetrized LP
from scipy.optimize import linprog
NPTS = np.array([49, 294, 168], dtype=float)
assert np.array_equal(n123[0], [49, 294, 168]) and np.array_equal(n123[-1], [0, 0, 0])
KEEP = np.arange(len(c334)) != len(c334) - 1   # exclude S = 0 (the tensor itself): only nonzero S give capacities
print(f"LP constraints: {int(KEEP.sum())} classes (all nonzero S, including S = A), plus sum = r and the type inequality")
for tabname, tab_all in (("Wang334", wang334), ("seeded", seeded)):
    tab = tab_all[KEEP]
    n123k = n123[KEEP]
    for r in (24, 25, 26):
        A_ub = n123k.astype(float)
        b_ub = (r - tab).astype(float)
        A_ub2 = np.vstack([A_ub, -np.array([49, 588, 504], float)])
        b_ub2 = np.concatenate([b_ub, [-36.0]])
        feas = linprog(np.zeros(3), A_ub=A_ub2, b_ub=b_ub2, A_eq=NPTS[None, :], b_eq=[float(r)], bounds=[(0, None)] * 3,
                       method="highs")
        mx = linprog(-NPTS, A_ub=A_ub, b_ub=b_ub, bounds=[(0, None)] * 3, method="highs")
        line = f"LP {tabname} r={r}: feasible(sum=r, caps, type)={feas.status == 0}"
        if feas.status == 0:
            w = feas.x
            slack = b_ub - A_ub @ w
            line += f" w=({w[0]:.4f},{w[1]:.4f},{w[2]:.4f}) min slack {slack.min():.4f} at class {int(slack.argmin())}"
        line += f"; max sum under caps only = {-mx.fun:.4f}" if mx.status == 0 else f"; max-LP status {mx.status}"
        print(line)
        if feas.status == 0:
            # exact re-check of the found point with rationals (rounded to 1e-9 then verified)
            from fractions import Fraction
            wf = [Fraction(x).limit_denominator(10**6) for x in feas.x]
            tot = sum(Fraction(int(NPTS[q])) * wf[q] for q in range(3))
            if tot != r:   # rescale the rational point onto sum = r and re-check
                wf = [x * Fraction(r) / tot for x in wf]
            okc = all(sum(int(n123k[i, q]) * wf[q] for q in range(3)) <= int(r - tab[i]) for i in range(len(tab)))
            okt = 49 * wf[0] + 588 * wf[1] + 504 * wf[2] >= 36
            print(f"   exact check of a rational point: caps {okc}, type {okt}, w = {[str(x) for x in wf]}")
print(f"done in {time.time()-t0:.1f}s")
