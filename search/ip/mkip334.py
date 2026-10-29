#!/usr/bin/env python3
"""Write coset-profile IP files for <3,3,4> mod P in the format read by the 3x3 project's enumerator (lineenum9x):
  'R <L> N 255', the 255 labels (a 9-bit representative of each nonzero coset of P, in our coset order 1..255),
  one row 'C <dim S'> <cap> <size> <label indices>' per strict superspace S' of P (cap = L - lb(S')),
  'G <|Stab(P)|>' and one line per element of Stab(P) in G0 = {a -> P a Q} (the induced permutation of the labels).
usage: mkip334.py P_CLASS TABLE(wang|seeded) L OUTFILE [--data DIR]   (reads DIR/sup_P<P_CLASS>.npz, DIR/seeded334.npz)
"""
import sys, time
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common334 import build_img0

DATA = "./"
if "--data" in sys.argv:   # directory of seeded334.npz and sup_P<cls>.npz (default: the current directory)
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
t0 = time.time()
Pc, tabname, L, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
z = np.load(DATA + f"sup_P{Pc}.npz")
t = np.load(DATA + "seeded334.npz")
table = t["wang334"] if tabname == "wang" else t["seeded"]
P, LP = int(z["P"]), z["LP"].astype(np.int64)
cls, dims, mptr, mem = z["cls"], z["dims"], z["mptr"], z["mem"].astype(np.int64)
lb = table[cls].astype(np.int64)
cap = L - lb
assert (cap >= 0).all(), "a strict superspace has lb > L (monotone case): no IP needed"
rep = np.zeros(256, np.int64)
for v in range(511, 0, -1):          # smallest representative of each coset
    if LP[v]:
        rep[LP[v]] = v
assert (rep[1:] > 0).all() and LP[P] == 0
img = build_img0()
stab = np.nonzero(img[:, P] == P)[0]
perms = LP[img[stab][:, rep[1:]]] - 1          # label l = coset l+1 -> label of the image coset
assert perms.min() >= 0 and all(len(set(p)) == 255 for p in perms[:5])
with open(out, "w") as f:
    f.write(f"R {L} N 255\n")
    f.write(" ".join(str(int(v)) for v in rep[1:]) + "\n")
    for s in range(len(cls)):
        m = mem[mptr[s]:mptr[s + 1]] - 1
        f.write(f"C {int(dims[s])} {int(cap[s])} {len(m)} " + " ".join(map(str, m.tolist())) + "\n")
    f.write(f"G {len(stab)}\n")
    for p in perms:
        f.write(" ".join(map(str, p.tolist())) + "\n")
pc = np.bincount(cap[dims == 2], minlength=4)
print(f"P {Pc} table {tabname} L {L}: rows {len(cls)}, group {len(stab)}, point caps 0/1/2/3: {pc[:4].tolist()}, "
      f"wrote {out} ({time.time()-t0:.1f}s)")
