#!/usr/bin/env python3
"""joinfin.py: the join layer for a point stage's Fin (the stage707_v6 method of join6.py,
made generic): usage  joinfin.py NS IPNS FIN AX OUTD [LIMIT]   (e.g. S708 H708 lean/.../S708/Fin.lean ... jout 1500)

Reads the generated Fin (module-level-join form; job blocks `have r<q> : ∀ k, A ≤ k → k < B → JobOK ...`) and writes
into OUTD/B334/E1x/Pts/<NS>/:
* TBJ / TGJ (core): topBlkJ / topGlueJ = the Fin's topBlk / topGlue proofs, importing the TB / TG modules;
* G<g> (Mathlib): the job blocks as top-level theorems jr6_<q> (verbatim, dedented), <= LIMIT lines per module, each
  importing only the check modules its blocks name, joined into grp6_<g>;
* Fin.new: the Fin with topBlk := topBlkJ, topGlue := topGlueJ and hjobs = an fa_join chain over grp6_<g>;
and OUTD/joinlayer.txt (the layer line TBJ TGJ G0 ...). Measured for 707 (stage707_v6): G modules ~6.9 GB, Fin
~6.8 GB, TBJ/TGJ ~1.5 GB.
"""
import os
import re
import sys

NS, IPNS, FIN, AX, OUTD = sys.argv[1:6]
LIMIT = int(sys.argv[6]) if len(sys.argv) > 6 else 1500
M = "B334.E1x.Pts.%s" % NS
REL = "B334/E1x/Pts/%s" % NS
P = os.path.join(OUTD, REL)
fin = open(FIN).read().split("\n")
imports = [l for l in fin if l.startswith("import ")]
other_imports = [l for l in imports if not l.startswith("import %s." % M)]
mods = [l[len("import %s." % M):] for l in imports if l.startswith("import %s." % M)]
tbmods = [m for m in mods if re.match(r"^TB\d+$", m)]
tgmods = [m for m in mods if re.match(r"^TG\d+$", m)]
kmods = {}
for m in mods:
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
header = fin[first_body:iTB]
tb_stmt, tb_proof = fin[iTB], fin[iTB + 1:iTG]
tg_stmt, tg_proof = fin[iTG], fin[iTG + 1:iLen]
mid = fin[iLen:iJobs]
tail = fin[iEnum:]
assert tb_stmt.endswith(":= by") and tg_stmt.endswith(":= by")
for pr in (tb_proof, tg_proof):
    while pr and pr[-1] == "":
        pr.pop()
JT = "JobOK CL Pts.%s.sl Pts.%s.UB (HT.entry k)" % (IPNS, IPNS)
rhead = re.compile(r"^  have r(\d+) : (∀ k, (\d+) ≤ k → k < (\d+) → " + re.escape(JT) + r") :=( by)?$")
blocks, cur = [], None
for l in fin[iJobs + 1:iEnum]:
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
for bl in blocks:
    txt = "\n".join(bl["lines"])
    used = set("J%s" % j for j in re.findall(r"\bJL_(\d+)\b", txt))
    for k in re.findall(r"\bK(\d+)\.lits\b", txt):
        assert ("K%sL" % k) in kmods.get(int(k), []), "no K%sL import" % k
        used.update(kmods[int(k)])
    for u in used:
        assert u in mods, "block r%d names %s, not imported by the Fin" % (bl["q"], u)
    bl["mods"] = used
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
OPTS = "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"


def write(path, text):
    with open(path, "x") as f:
        f.write(text)


write(os.path.join(P, "TBJ.lean"),
      "import %s.Ctx\nimport %s.TopL\nimport %s.HT\nimport B334.E1x.IPChk\n" % (M, M, M) +
      "".join("import %s.%s\n" % (M, m) for m in tbmods) + "\n" + OPTS +
      "/-! # The joined top-chain block facts of `%s`: the generated Fin's `topBlk` proof -/\n\n" % NS +
      "namespace %s\n\n" % M + tb_stmt.replace("theorem topBlk :", "theorem topBlkJ :", 1) + "\n" +
      "\n".join(tb_proof) + "\n\nend %s\n" % M)
write(os.path.join(P, "TGJ.lean"),
      "import %s.TopL\nimport %s.HT\nimport B334.E1x.Pts.ChkB\n" % (M, M) +
      "".join("import %s.%s\n" % (M, m) for m in tgmods) + "\n" + OPTS +
      "/-! # The joined top-chain glue facts of `%s`: the generated Fin's `topGlue` proof -/\n\n" % NS +
      "namespace %s\n\n" % M + tg_stmt.replace("theorem topGlue :", "theorem topGlueJ :", 1) + "\n" +
      "\n".join(tg_proof) + "\n\nend %s\n" % M)
gn = []
for gi, g in enumerate(groups):
    used = sorted(set(m for bl in g for m in bl["mods"]), key=lambda s: (len(s), s))
    a0, b0 = g[0]["a"], g[-1]["b"]
    out = ["import %s.Ctx\nimport %s.HT\nimport B334.E1x.Pts.ChkB\nimport B334.E1x.Pts.JobS\nimport B334.E1x.Pts.%s.F\n" % (
        M, M, IPNS)]
    out += ["import %s.%s\n" % (M, m) for m in used]
    out.append("\n" + OPTS)
    out.append("/-! # Joined job facts of `%s`, jobs %d … %d: the generated Fin's job blocks r%d … r%d as\n"
               "theorems, joined into `grp6_%d` -/\n\n" % (NS, a0, b0 - 1, g[0]["q"], g[-1]["q"], gi))
    out.append("namespace %s\nopen B334 B334.E1x B334.E1x.E1PS\n\n" % M)
    for bl in g:
        out.append("theorem jr6_%d : %s :=%s\n" % (bl["q"], bl["T"], " by" if bl["by"] else ""))
        lines = list(bl["lines"])
        while lines and lines[-1] == "":
            lines.pop()
        out.append("\n".join(lines) + "\n")
    out.append("\ntheorem grp6_%d : ∀ k, %d ≤ k → k < %d → %s := by\n" % (gi, a0, b0, JT))
    out.append("  have a0 := jr6_%d\n" % g[0]["q"])
    for t, bl in enumerate(g[1:], 1):
        out.append("  have a%d := Pts.fa_join a%d jr6_%d\n" % (t, t - 1, bl["q"]))
    out.append("  exact a%d\n\nend %s\n" % (len(g) - 1, M))
    write(os.path.join(P, "G%d.lean" % gi), "".join(out))
    gn.append(gi)
hj = ["theorem hjobs : ∀ k < nJ, %s := by" % JT, "  have a0 := grp6_0"]
for t in range(1, len(gn)):
    hj.append("  have a%d := Pts.fa_join a%d grp6_%d" % (t, t - 1, t))
hj.append("  exact fun k hk => a%d k (Nat.zero_le k) hk" % (len(gn) - 1))
newfin = (["import %s.TBJ" % M, "import %s.TGJ" % M] + ["import %s.G%d" % (M, gi) for gi in gn] + other_imports +
          header + [tb_stmt.replace(":= by", ":= topBlkJ"), "", tg_stmt.replace(":= by", ":= topGlueJ"), ""] + mid + hj +
          [""] + tail)
txt = "\n".join(newfin)
assert "sorry" not in txt
write(os.path.join(P, "Fin.new"), txt)
with open(os.path.join(OUTD, "joinlayer.txt"), "x") as f:
    f.write(" ".join(["%s/TBJ" % REL, "%s/TGJ" % REL] + ["%s/G%d" % (REL, gi) for gi in gn]) + "\n")
print("joinfin %s: blocks %d (jobs 0 … %d), groups %d (LIMIT %d), Fin %d -> %d lines, max imports per group %d" % (
    NS, len(blocks), blocks[-1]["b"] - 1, len(groups), LIMIT, len(fin), len(newfin),
    max(len(set(m for bl in g for m in bl["mods"])) for g in groups)))
