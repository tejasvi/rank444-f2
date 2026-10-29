#!/usr/bin/env python3
"""Row classes of a point IP, and raised point IPs (caps of listed classes lowered by 1).
  mkcand.py classes P OUT_ROWCLS          : one G0-class id per C row of ip_P<P>_seeded_L*.txt (file order = sup_P<P>.npz order)
  mkcand.py raise IN_IP P CLASSES OUT_IP  : IN_IP with every cap of the listed classes (comma-separated) lowered by 1
Both read DIR/sup_P<P>.npz, DIR given by --data DIR (default: the current directory).
"""
import sys
import numpy as np

DATA = "./"
if "--data" in sys.argv:   # directory of seeded334.npz and sup_P<cls>.npz (default: the current directory)
    _i = sys.argv.index("--data"); DATA = sys.argv[_i + 1].rstrip("/") + "/"; del sys.argv[_i:_i + 2]
mode = sys.argv[1]
if mode == "classes":
    P, out = int(sys.argv[2]), sys.argv[3]
    cls = np.load(DATA + f"sup_P{P}.npz")["cls"].astype(np.int64)
    with open(out, "w") as f:
        f.write("\n".join(str(int(c)) for c in cls) + "\n")
    print(f"wrote {out}: {len(cls)} rows")
elif mode == "raise":
    src, P, lst, out = sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
    sel = set(int(x) for x in lst.split(","))
    cls = np.load(DATA + f"sup_P{P}.npz")["cls"].astype(np.int64)
    lines = open(src).read().split("\n")
    s = 0; nlow = 0; neg = 0
    for i, ln in enumerate(lines):
        if ln.startswith("C "):
            f = ln.split()
            if int(cls[s]) in sel:
                cap = int(f[2]) - 1
                if cap < 0:
                    neg += 1
                f[2] = str(max(cap, 0)); lines[i] = " ".join(f); nlow += 1
            s += 1
        elif ln.startswith("G "):
            break
    assert s == len(cls), (s, len(cls))
    open(out, "w").write("\n".join(lines))
    print(f"wrote {out}: {nlow} caps lowered ({neg} would go below 0, set to 0)")
