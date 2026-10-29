#!/usr/bin/env python3
"""label-value -> coset maps for the completion of point leaves: OUTDIR/lab2cos_P<cls>.txt lines 'labelvalue coset'
(label values are the 9-bit coset representatives written by lineenum; cosets are the 8-bit L_P coordinates of q<P>.t)
usage: s4_labmaps.py OUTDIR [--data DIR]   (reads DIR/sup_P706.npz, sup_P707.npz, sup_P708.npz)"""
import os
import sys
import numpy as np
DATA = "./"
if "--data" in sys.argv:
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
OUT = sys.argv[1]
for cls in (706, 707, 708):
    LP = np.load(DATA + f"sup_P{cls}.npz")["LP"].astype(int)
    rep = {}
    for v in range(511, 0, -1):
        if LP[v]:
            rep[int(LP[v])] = v
    with open(os.path.join(OUT, f"lab2cos_P{cls}.txt"), "w") as f:
        for c in range(1, 256):
            f.write(f"{rep[c]} {c}\n")
    print(cls, "written")
