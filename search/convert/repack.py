#!/usr/bin/env python3
"""repack.py [STAGE_V3 [TIMES]]: stage 707 v5 = the big-job (K) check modules of stage707_v3 that did not all
build in the first build of the S707 modules, re-packed by predicted kernel memory, plus v3's Fin (imports adjusted) and Ax.

Inputs: STAGE_V3 (default ../stage707_v3: the output of the S707 version of conv_e1p.py run, with its lean/ sources and
data/k<k>.bin) and TIMES (default e707_times.txt: the build times and peak memory of the first build of these modules).
Memory model per piece of B Kbit: C1*B + C2*B^2 GB (fit to two probe builds); a part (one kb/kg theorem pair) is the sum
over its pieces; parts are grouped into modules K<k>Q<q> with predicted sum <= BUD GB (BUD from the calibration on the
K modules that built: scale = max (maxrss - 1.5 GB) / predicted; BUD = 10 GB / scale). Theorem names and statements
are copied verbatim from v3, so v3's Fin joins them unchanged; only its imports change.
"""
import os
import re
import sys

S = sys.argv[1] if len(sys.argv) > 1 else "../stage707_v3"
P = S + "/lean/B334/E1x/Pts/S707/"
C1, C2 = 3.14e-3, 6.35e-6


def mem(bits):
    kb = bits / 1000.0
    return C1 * kb + C2 * kb * kb


def lit_bits(path):
    b = open(path, "rb").read()
    n = int.from_bytes(b[:4], "little")
    off, out = 4, []
    for _ in range(n):
        nb = int.from_bytes(b[off:off + 4], "little")
        off += 4 + nb
        out.append(8 * nb)
    assert off == len(b), path
    return out


times = {}
for line in open(sys.argv[2] if len(sys.argv) > 2 else "e707_times.txt"):
    t = line.split()
    if len(t) < 2:
        continue
    kb = None
    for i, x in enumerate(t):
        if x == "KB":
            kb = int(t[i - 1])
    times[t[0]] = (t[1], kb)

thm_re = re.compile(r"^theorem (kb|kg)_(\d+)_(\d+) : .* (\d+) (\d+) = true := by(?: decide \+kernel)?$")
jobs = {}      # k -> {"mods": [name], "parts": {lo: (m, [lines])}}
for fn in sorted(os.listdir(P)):
    mm = re.match(r"K(\d+)C(\d+)\.lean$", fn)
    if not mm:
        continue
    k = int(mm.group(1))
    j = jobs.setdefault(k, {"mods": [], "parts": {}})
    j["mods"].append(fn[:-5])
    lines = open(P + fn).read().split("\n")
    i = 0
    while i < len(lines):
        m2 = thm_re.match(lines[i])
        if m2:
            kind, kk, lo, lo2, m = m2.group(1), int(m2.group(2)), int(m2.group(3)), int(m2.group(4)), int(m2.group(5))
            assert kk == k and lo == lo2, lines[i]
            block = [lines[i]]
            if not lines[i].endswith("decide +kernel"):
                block.append(lines[i + 1])
                assert lines[i + 1] == "  decide +kernel", lines[i + 1]
                i += 1
            ent = j["parts"].setdefault(lo, [m, {}])
            assert ent[0] == m
            ent[1][kind] = block
        i += 1

# calibration on the built K modules
cal = []
for k, j in jobs.items():
    bits = lit_bits(S + "/data/k%d.bin" % k)
    j["bits"] = bits
for k, j in jobs.items():
    for name in j["mods"]:
        txt = open(P + name + ".lean").read()
        los = [int(x) for x in re.findall(r"^theorem kb_%d_(\d+) " % k, txt, re.M)]
        pred = sum(mem(j["bits"][i]) for lo in los for i in range(lo, lo + j["parts"][lo][0]))
        st = times.get("B334/E1x/Pts/S707/" + name)
        if st:
            cal.append((st[0], st[1] / 1e6 if st[1] else None, pred, name))
ok = [(gb - 1.5) / p for rc, gb, p, n in cal if rc == "rc=0" and gb and p > 0.5]
scale = max(ok) if ok else 2.0
BUD = 10.0 / scale
print("calibration: %d K modules with times (%d ok), scale max (maxrss-1.5)/pred = %.2f, BUD = %.2f GB predicted" % (
    len(cal), sum(1 for c in cal if c[0] == "rc=0"), scale, BUD))
for rc, gb, p, n in sorted(cal, key=lambda c: -c[2])[:12]:
    print("  %s %s maxrss %.1f GB predicted %.2f" % (n, rc, gb or -1, p))
fails = [c for c in cal if c[0] != "rc=0"]
print("failed modules: %d, their predicted min %.2f" % (len(fails), min(c[2] for c in fails) if fails else 0))

# jobs to re-pack: any module not built OK
os.makedirs("lean/B334/E1x/Pts/S707", exist_ok=False)
os.makedirs("data", exist_ok=False)
with open("data/NONE.txt", "x") as f:
    f.write("stage707_v5 needs no data files: its modules import v3's literal modules\n")
newmods, repl = [], {}
hdr_tpl = """import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K%(k)dL
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job %(k)d of `S707`, parts %(lo)d … %(hi)d, re-packed by predicted kernel memory (%(pred).2f of %(bud).2f GB;
stage707_v5; the theorems are v3's `K%(k)dC*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

"""
nrep = 0
for k in sorted(jobs):
    j = jobs[k]
    built = all(times.get("B334/E1x/Pts/S707/" + n, ("none",))[0] == "rc=0" for n in j["mods"])
    if built:
        continue
    nrep += 1
    los = sorted(j["parts"])
    pm = [(lo, sum(mem(j["bits"][i]) for i in range(lo, lo + j["parts"][lo][0]))) for lo in los]
    groups, cur, cs = [], [], 0.0
    for lo, p in pm:
        if cur and cs + p > BUD:
            groups.append((cur, cs))
            cur, cs = [], 0.0
        cur.append(lo)
        cs += p
    if cur:
        groups.append((cur, cs))
    names = []
    for q, (g, cs) in enumerate(groups):
        nm = "K%dQ%d" % (k, q)
        hi = g[-1] + j["parts"][g[-1]][0] - 1
        body = []
        for lo in g:
            body.extend(j["parts"][lo][1]["kb"])
            body.extend(j["parts"][lo][1]["kg"])
        with open("lean/B334/E1x/Pts/S707/%s.lean" % nm, "x") as f:
            f.write(hdr_tpl % {"k": k, "lo": g[0], "hi": hi, "pred": cs, "bud": BUD})
            f.write("\n".join(body) + "\n\nend B334.E1x.Pts.S707\n")
        names.append(nm)
        newmods.append((nm, cs))
    for n in j["mods"]:
        repl[n] = names
print("re-packed jobs: %d; new modules: %d (predicted max %.2f GB)" % (nrep, len(newmods), max(c for _, c in newmods)))

# Fin with adjusted imports, and Ax
fin = open(P + "Fin.lean").read().split("\n")
out, done = [], set()
for line in fin:
    m3 = re.match(r"^import B334\.E1x\.Pts\.S707\.(K\d+C\d+)$", line)
    if m3 and m3.group(1) in repl:
        for nm in repl[m3.group(1)]:
            if nm not in done:
                out.append("import B334.E1x.Pts.S707.%s" % nm)
                done.add(nm)
        continue
    out.append(line)
with open("lean/B334/E1x/Pts/S707/Fin.lean", "x") as f:
    f.write("\n".join(out))
with open("lean/B334/E1x/Pts/S707/Ax.lean", "x") as f:
    f.write(open(P + "Ax.lean").read())
with open("layers.txt", "x") as f:
    f.write(" ".join("B334/E1x/Pts/S707/%s" % n for n, _ in newmods) + "\n")
    f.write("B334/E1x/Pts/S707/Fin\nB334/E1x/Pts/S707/Ax\n")
print("stage707_v5: %d new K modules + Fin + Ax" % len(newmods))
