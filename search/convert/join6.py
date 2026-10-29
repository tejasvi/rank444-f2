#!/usr/bin/env python3
"""join6.py [LIMIT]: stage707_v6 = join modules + a small Fin for the 707 point run, from the v5 Fin
(fin_v5.lean = v3's Fin with the re-packed jobs' imports), without rebuilding any check module.

The v5 Fin (42K lines) aborted at the 15 GB cap in its first build. Its proofs are kept verbatim but distributed:
* TBJ / TGJ (core Lean): topBlkJ / topGlueJ = the Fin's topBlk / topGlue joins over the TB / TG check modules;
* G<g> (Mathlib): the Fin's job blocks `have r<q> : T := P` become top-level theorems `jr6_<q> : T := P` (same text,
  dedented), about LIMIT lines per module, each module importing only the check modules its blocks name; `grp6_<g>`
  joins its blocks with `Pts.fa_join` into `∀ k, a ≤ k → k < b → JobOK ...`;
* Fin: topBlk := topBlkJ, topGlue := topGlueJ, hjobs joins the grp6_<g>; the rest of the v5 Fin unchanged; Ax as v5.
Also writes test copies (namespace T7J, `open B334.E1x.Pts.S707`) of TBJ, TGJ, G0 and FinT (Fin with the groups after
G0 as `sorry`) into test/ for a memory measurement; they are not stage modules.
Run in a directory that holds fin_v5.lean and ax_v5.lean (the Fin and Ax modules written by repack.py).
"""
import os
import re
import sys

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
M = "B334.E1x.Pts.S707"
P = "lean/B334/E1x/Pts/S707"
fin = open("fin_v5.lean").read().split("\n")
ax = open("ax_v5.lean").read()

imports = [l for l in fin if l.startswith("import ")]
other_imports = [l for l in imports if not re.match(r"^import B334\.E1x\.Pts\.S707\.", l)]
s707 = [l[len("import " + M + "."):] for l in imports if l.startswith("import " + M + ".")]
tbmods = [m for m in s707 if re.match(r"^TB\d+$", m)]
tgmods = [m for m in s707 if re.match(r"^TG\d+$", m)]
kmods = {}
for m in s707:
    mm = re.match(r"^K(\d+)([CQ]\d+|L)$", m)
    if mm:
        kmods.setdefault(int(mm.group(1)), []).append(m)
assert tbmods and tgmods, "TB/TG imports"


def find(prefix):
    for i, l in enumerate(fin):
        if l.startswith(prefix):
            return i
    raise SystemExit("missing %r" % prefix)


iTB, iTG, iLen, iJobs, iEnum = (find("theorem topBlk :"), find("theorem topGlue :"), find("theorem topLen :"),
                                find("theorem hjobs :"), find("theorem enum :"))
assert iTB < iTG < iLen < iJobs < iEnum
first_body = max(i for i, l in enumerate(fin[:iTB]) if l.startswith("import ")) + 1
header = fin[first_body:iTB]          # set_option, docstring, namespace, open
tb_stmt, tb_proof = fin[iTB], fin[iTB + 1:iTG]
tg_stmt, tg_proof = fin[iTG], fin[iTG + 1:iLen]
mid = fin[iLen:iJobs]                  # topLen, hroot
tail = fin[iEnum:]
assert tb_stmt.endswith(":= by") and tg_stmt.endswith(":= by")
while tg_proof and tg_proof[-1] == "":
    tg_proof.pop()
while tb_proof and tb_proof[-1] == "":
    tb_proof.pop()

# the job blocks
body = fin[iJobs + 1:iEnum]
blocks, cur = [], None
rhead = re.compile(r"^  have r(\d+) : (∀ k, (\d+) ≤ k → k < (\d+) → JobOK CL Pts\.H707\.sl Pts\.H707\.UB \(HT\.entry k\)) :=( by)?$")
for l in body:
    m = rhead.match(l)
    if m:
        cur = {"q": int(m.group(1)), "T": m.group(2), "a": int(m.group(3)), "b": int(m.group(4)), "by": bool(m.group(5)),
               "lines": []}
        blocks.append(cur)
        continue
    if l.startswith("  have a0 :="):
        cur = None
        continue
    if cur is not None:
        assert l.startswith("    ") or l == "", "unexpected line in a job block: %r" % l[:80]
        cur["lines"].append(l[2:] if l else l)
assert blocks and blocks[0]["a"] == 0, "first block"
for x, y in zip(blocks, blocks[1:]):
    assert x["b"] == y["a"], "blocks not adjacent at r%d" % x["q"]
nJ = blocks[-1]["b"]
for bl in blocks:
    txt = "\n".join(bl["lines"])
    mods = set()
    for j in re.findall(r"\bJL_(\d+)\b", txt):
        mods.add("J%s" % j)
    for k in re.findall(r"\bK(\d+)\.lits\b", txt):
        mods.update(kmods.get(int(k), []))
        assert ("K%sL" % k) in kmods.get(int(k), []), "no K%sL import" % k
    for m in mods:
        assert m in s707, "block r%d names %s, not imported by the v5 Fin" % (bl["q"], m)
    bl["mods"] = sorted(mods)
    bl["n"] = len(bl["lines"]) + 1

groups, g, gl = [], [], 0
for bl in blocks:
    if g and gl + bl["n"] > LIMIT:
        groups.append(g)
        g, gl = [], 0
    g.append(bl)
    gl += bl["n"]
if g:
    groups.append(g)

os.makedirs(P, exist_ok=False)
os.makedirs("data", exist_ok=False)
os.makedirs("test/T7J", exist_ok=False)
with open("data/NONE.txt", "x") as f:
    f.write("stage707_v6 needs no data files: its modules import the check modules\n")
OPTS = "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"
mods_written = []


def write(path, text):
    with open(path, "x") as f:
        f.write(text)


def ns_test(text):
    """the test copy: namespace T7J with S707 opened (theorem names land in T7J)"""
    text = text.replace("namespace %s\n" % M, "namespace B334.E1x.Pts.T7J\nopen %s\n" % M, 1)
    text = text.replace("end %s\n" % M, "end B334.E1x.Pts.T7J\n")
    return re.sub(r"^import B334\.E1x\.Pts\.S707\.(TBJ|TGJ|G\d+)$", r"import B334.E1x.Pts.T7J.\1", text, flags=re.M)


tbj = ("import %s.Ctx\nimport %s.TopL\nimport %s.HT\nimport B334.E1x.IPChk\n" % (M, M, M) +
       "".join("import %s.%s\n" % (M, m) for m in tbmods) + "\n" + OPTS +
       "/-! # The joined top-chain block facts of `S707` (stage707_v6): the v5 Fin's `topBlk` proof -/\n\n" +
       "namespace %s\n\n" % M + tb_stmt.replace("theorem topBlk :", "theorem topBlkJ :", 1) + "\n" +
       "\n".join(tb_proof) + "\n\nend %s\n" % M)
tgj = ("import %s.TopL\nimport %s.HT\nimport B334.E1x.Pts.ChkB\n" % (M, M) +
       "".join("import %s.%s\n" % (M, m) for m in tgmods) + "\n" + OPTS +
       "/-! # The joined top-chain glue facts of `S707` (stage707_v6): the v5 Fin's `topGlue` proof -/\n\n" +
       "namespace %s\n\n" % M + tg_stmt.replace("theorem topGlue :", "theorem topGlueJ :", 1) + "\n" +
       "\n".join(tg_proof) + "\n\nend %s\n" % M)
write("%s/TBJ.lean" % P, tbj)
write("%s/TGJ.lean" % P, tgj)
write("test/T7J/TBJ.lean", ns_test(tbj))
write("test/T7J/TGJ.lean", ns_test(tgj))
gnames = []
for gi, g in enumerate(groups):
    mods = sorted(set(m for bl in g for m in bl["mods"]), key=lambda s: (len(s), s))
    a0, b0 = g[0]["a"], g[-1]["b"]
    out = ["import %s.Ctx\nimport %s.HT\nimport B334.E1x.Pts.ChkB\nimport B334.E1x.Pts.JobS\nimport B334.E1x.Pts.H707.F\n" % (M, M)]
    out += ["import %s.%s\n" % (M, m) for m in mods]
    out.append("\n" + OPTS)
    out.append("/-! # Joined job facts of `S707`, jobs %d … %d (stage707_v6): the v5 Fin's job blocks r%d … r%d as\n"
               "theorems, joined into `grp6_%d` -/\n\n" % (a0, b0 - 1, g[0]["q"], g[-1]["q"], gi))
    out.append("namespace %s\nopen B334 B334.E1x B334.E1x.E1PS\n\n" % M)
    for bl in g:
        out.append("theorem jr6_%d : %s :=%s\n" % (bl["q"], bl["T"], " by" if bl["by"] else ""))
        lines = list(bl["lines"])
        while lines and lines[-1] == "":
            lines.pop()
        out.append("\n".join(lines) + "\n")
    out.append("\ntheorem grp6_%d : ∀ k, %d ≤ k → k < %d → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by\n" % (gi, a0, b0))
    out.append("  have a0 := jr6_%d\n" % g[0]["q"])
    for t, bl in enumerate(g[1:], 1):
        out.append("  have a%d := Pts.fa_join a%d jr6_%d\n" % (t, t - 1, bl["q"]))
    out.append("  exact a%d\n\nend %s\n" % (len(g) - 1, M))
    text = "".join(out)
    write("%s/G%d.lean" % (P, gi), text)
    if gi == 0:
        write("test/T7J/G0.lean", ns_test(text))
    gnames.append((gi, a0, b0))

finhdr = (["import %s.TBJ" % M, "import %s.TGJ" % M] + ["import %s.G%d" % (M, gi) for gi, _, _ in gnames] +
          other_imports)
hj = ["theorem hjobs : ∀ k < nJ, JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by", "  have a0 := grp6_0"]
for t in range(1, len(gnames)):
    hj.append("  have a%d := Pts.fa_join a%d grp6_%d" % (t, t - 1, t))
hj.append("  exact fun k hk => a%d k (Nat.zero_le k) hk" % (len(gnames) - 1))
fin6 = (finhdr + header + [tb_stmt.replace(":= by", ":= topBlkJ"), "", tg_stmt.replace(":= by", ":= topGlueJ"), ""] +
        mid + hj + [""] + tail)
fintext = "\n".join(fin6)
assert "sorry" not in fintext
write("%s/Fin.lean" % P, fintext)
write("%s/Ax.lean" % P, ax)
# FinT: G0 real, the other groups as one sorry
hjt = ["theorem hjobs : ∀ k < nJ, JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by", "  have a0 := grp6_0",
       "  have rest : ∀ k, %d ≤ k → k < nJ → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := sorry" % gnames[0][2],
       "  exact fun k hk => (Pts.fa_join a0 rest) k (Nat.zero_le k) hk"]
fint = ["import B334.E1x.Pts.T7J.TBJ", "import B334.E1x.Pts.T7J.TGJ", "import B334.E1x.Pts.T7J.G0"] + other_imports
fint += header + [tb_stmt.replace(":= by", ":= topBlkJ"), "", tg_stmt.replace(":= by", ":= topGlueJ"), ""] + mid + hjt
fint += [""] + tail
ft = "\n".join(fint)
ft = ft.replace("namespace %s\n" % M, "namespace B334.E1x.Pts.T7J\nopen %s\n" % M, 1).replace("end %s" % M, "end B334.E1x.Pts.T7J")
write("test/T7J/FinT.lean", ft)
with open("layers.txt", "x") as f:
    f.write(" ".join(["%s/TBJ" % P[5:], "%s/TGJ" % P[5:]] + ["%s/G%d" % (P[5:], gi) for gi, _, _ in gnames]) + "\n")
    f.write("%s/Fin\n%s/Ax\n" % (P[5:], P[5:]))
print("blocks %d (jobs 0 … %d), groups %d (LIMIT %d lines), group sizes %s" % (
    len(blocks), nJ - 1, len(groups), LIMIT, ",".join(str(sum(b["n"] for b in g)) for g in groups)))
print("imports per group: %s" % ",".join(str(len(set(m for bl in g for m in bl["mods"]))) for g in groups))
print("Fin lines %d (v5: %d); TB modules %d, TG modules %d" % (len(fin6), len(fin), len(tbmods), len(tgmods)))
