# mk_fin_join.awk (run by mk_fin_join.sh, see there). Inputs: the J/K symbol index
# ("symbol module" lines), then the old Fin. Variables: NSN (run name, e.g. R619), LIM, MXB (group limits), NJV (nJ of
# the run's HT), DIR (output directory), SCD (scratch directory for layers.txt).
function die(msg) { print "ERROR: " msg; err = 1; exit 1 }
function fixdec(s) {
  gsub(/:= by decide$/, ":= by decide +kernel", s)
  gsub(/; decide\)/, "; decide +kernel)", s)
  gsub(/\(by decide\)/, "(by decide +kernel)", s)
  return s
}
function find(re,   i) { for (i = 1; i <= n; i++) if (L[i] ~ re) return i; die("missing " re) }
function lastNE(a, b,   i) { for (i = b; i >= a; i--) if (L[i] != "") return i; return a - 1 }
function modkey(m,   a, b) {
  if (m ~ /^J[0-9]+$/) return sprintf("1 %08d", substr(m, 2) + 0)
  if (m ~ /^K[0-9]+L$/) { a = m; gsub(/[^0-9]/, "", a); return sprintf("2 %08d 0", a + 0) }
  a = m; sub(/^K/, "", a); sub(/C.*$/, "", a); b = m; sub(/^.*C/, "", b)
  return sprintf("2 %08d 1 %04d", a + 0, b + 0)
}
function opts(f) { printf "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n" > f }
# the proof of a join theorem (statement at line a, proof up to line b). If the statement's bound is a name (NT, from
# HT), the last step rewrites it to the last join's literal bound explicitly, `rw [show NT = n by decide +kernel]`, which
# also fails loudly if the name is unbound (an auto-bound variable: an earlier TBJ did not import HT)
function joinbody(f, a, b,   e, i, bnd, n, m1) {
  e = lastNE(a + 1, b)
  if (!match(L[a], / 0 ([A-Za-z0-9_.]+) = true := by$/, m1)) die("join statement bound: " L[a])
  bnd = m1[1]
  if (L[e] !~ /^  exact h[0-9]+$/ || !match(L[e - 1], /^  have h[0-9]+ : .* 0 ([0-9]+) = true := /, m1))
    die("join end at line " e)
  n = m1[1]
  for (i = a + 1; i < e; i++) print fixdec(L[i]) > f
  if (bnd !~ /^[0-9]+$/) printf "  rw [show %s = %s by decide +kernel]\n", bnd, n > f
  else if (bnd != n) die("join bound " bnd " vs " n)
  print L[e] > f
}
FNR == NR { MOD[$1] = $2; next }
{ L[++n] = $0 }
END {
  if (err) exit 1
  M = "B334.E1x." NSN
  iTB = find("^theorem topBlk : "); iTG = find("^theorem topGlue : "); iLen = find("^theorem topLen : ")
  iJobs = find("^theorem hjobs : "); iA0 = find("^  have a0 := r0$"); iEnum = find("^theorem enum : ")
  iLeaf = find("^theorem leafAll : "); iHLF = find("^theorem hLF : ")
  if (!(iTB < iTG && iTG < iLen && iLen < iJobs && iJobs < iA0 && iA0 < iEnum && iEnum < iLeaf && iLeaf < iHLF))
    die("section order")
  if (L[iTB] !~ / := by$/ || L[iTG] !~ / := by$/ || L[iLeaf] !~ / := by$/ || L[iJobs] !~ / := by$/)
    die("topBlk/topGlue/leafAll/hjobs do not end in ':= by'")
  # imports of the old Fin: TB/TG/Lf go to the joins, J/K to the G modules, the rest stays in Fin
  last = 0; tb = ""; tg = ""; lf = ""; keep = ""
  for (i = 1; i < iTB; i++) if (L[i] ~ /^import /) {
    last = i; m = L[i]; sub(/^import /, "", m)
    if (index(m, M ".") == 1) {
      r = substr(m, length(M) + 2)
      if (r ~ /^TB[0-9]+$/) tb = tb "import " m "\n"
      else if (r ~ /^TG[0-9]+$/) tg = tg "import " m "\n"
      else if (r ~ /^Lf[0-9]+$/) lf = lf "import " m "\n"
      else if (r ~ /^(J[0-9]+|K[0-9]+L|K[0-9]+C[0-9]+)$/) HAVE[r] = 1
      else keep = keep "import " m "\n"
    } else keep = keep "import " m "\n"
  }
  if (tb == "" || tg == "" || lf == "") die("TB/TG/Lf imports")
  # the job blocks
  nb = 0
  for (i = iJobs + 1; i < iA0; i++) {
    s = L[i]
    if (s ~ /^  have r[0-9]+ : /) {
      nb++
      q = s; sub(/^  have r/, "", q); sub(/ .*$/, "", q); BQ[nb] = q
      T = s; sub(/^  have r[0-9]+ : /, "", T)
      BBY[nb] = (T ~ / := by$/) ? 1 : 0
      sub(/ :=( by)?$/, "", T); BT[nb] = T
      if (T !~ /^∀ k, [0-9]+ ≤ k → k < [0-9]+ → JobOK C sl UB \(HT\.entry k\)$/) die("block type r" q ": " T)
      a = T; sub(/^∀ k, /, "", a); sub(/ .*$/, "", a)
      b = T; sub(/^.* k < /, "", b); sub(/ .*$/, "", b)
      BA[nb] = a + 0; BB[nb] = b + 0; BN[nb] = 1; BL[nb] = ""; BMS[nb] = ""
      continue
    }
    if (nb == 0 || s !~ /^    /) die("unexpected line " i ": " substr(s, 1, 80))
    BL[nb] = BL[nb] fixdec(substr(s, 3)) "\n"; BN[nb]++
    t = s
    while (match(t, /(JL|JW|jr|KW)_[0-9]+|k[bg]_[0-9]+_[0-9]+|K[0-9]+[.]lits/)) {
      sym = substr(t, RSTART, RLENGTH); t = substr(t, RSTART + RLENGTH)
      if (!(sym in MOD)) die("block r" BQ[nb] ": no module defines " sym)
      mm = MOD[sym]
      if (!(mm in HAVE)) die("block r" BQ[nb] " names " mm ", not imported by the old Fin")
      if (!((nb, mm) in BSEEN)) { BSEEN[nb, mm] = 1; BMS[nb] = BMS[nb] " " mm }
    }
  }
  if (nb == 0 || BA[1] != 0) die("first block")
  for (j = 2; j <= nb; j++) if (BA[j] != BB[j - 1]) die("blocks not adjacent at r" BQ[j])
  if (BB[nb] != NJV + 0) die("last block ends at " BB[nb] ", nJ = " NJV)
  for (i = iA0 + 1; i < iEnum; i++) if (L[i] != "" && L[i] !~ /^  have a[0-9]+ := GJ\.fa_join a[0-9]+ r[0-9]+$/ &&
      L[i] !~ /^  exact fun k hk => a[0-9]+ k \(Nat\.zero_le k\) hk$/) die("unexpected join line " i)
  # groups: at most LIM lines and MXB blocks
  ng = 0; gl = 0; gb = 0
  for (j = 1; j <= nb; j++) {
    if (gb > 0 && (gl + BN[j] > LIM || gb >= MXB)) { ng++; gl = 0; gb = 0 }
    GRP[j] = ng; gl += BN[j]; gb++
  }
  ng++
  for (j = 1; j <= nb; j++) { g = GRP[j]; if (!(g in GF)) GF[g] = j; GG[g] = j; GLN[g] += BN[j] }
  # G modules
  for (g = 0; g < ng; g++) {
    delete GM; delete KEYS; delete SK; k = 0
    for (j = GF[g]; j <= GG[g]; j++) {
      nm = split(substr(BMS[j], 2), arr, " ")
      for (x = 1; x <= nm; x++) if (!(arr[x] in GM)) { GM[arr[x]] = 1; k++; KEYS[k] = modkey(arr[x]) "\t" arr[x] }
    }
    nk = asort(KEYS, SK); GIM[g] = nk
    f = DIR "/G" g ".lean"
    printf "import %s.F\nimport %s.HT\nimport B334.E1x.GJ.JobS\n", M, M > f
    for (x = 1; x <= nk; x++) { split(SK[x], kv, "\t"); printf "import %s.%s\n", M, kv[2] > f }
    printf "\n" > f; opts(f)
    a0 = BA[GF[g]]; b0 = BB[GG[g]]
    printf "/-! # Joined job facts of `%s`, jobs %d … %d: the generated Fin's job blocks r%s … r%s as\ntheorems (plain `decide` as `decide +kernel`), joined into `grpJ_%d` -/\n\n", NSN, a0, b0 - 1, BQ[GF[g]], BQ[GG[g]], g > f
    printf "namespace %s\nopen B334 B334.E1x B334.E1x.E1GS\n\n", M > f
    for (j = GF[g]; j <= GG[g]; j++) printf "theorem jrJ_%s : %s :=%s\n%s", BQ[j], BT[j], (BBY[j] ? " by" : ""), BL[j] > f
    printf "\ntheorem grpJ_%d : ∀ k, %d ≤ k → k < %d → JobOK C sl UB (HT.entry k) := by\n", g, a0, b0 > f
    printf "  have a0 := jrJ_%s\n", BQ[GF[g]] > f
    t = 0
    for (j = GF[g] + 1; j <= GG[g]; j++) { t++; printf "  have a%d := GJ.fa_join a%d jrJ_%s\n", t, t - 1, BQ[j] > f }
    printf "  exact a%d\n\nend %s\n", t, M > f
    close(f)
  }
  # TBJ, TGJ, LfJ
  f = DIR "/TBJ.lean"
  printf "%simport %s.TopL\nimport %s.HT\nimport B334.E1x.IPChk\n\n", tb, M, M > f; opts(f)
  printf "/-! # The joined top-chain block facts of `%s`: the generated Fin's `topBlk` proof -/\n\nnamespace %s\n\n", NSN, M > f
  s = L[iTB]; sub(/^theorem topBlk : /, "theorem topBlkJ : ", s); print s > f
  joinbody(f, iTB, iTG - 1)
  printf "\nend %s\n", M > f; close(f)
  f = DIR "/TGJ.lean"
  printf "%simport %s.TopL\nimport %s.HT\nimport B334.E1x.IPChk\n\n", tg, M, M > f; opts(f)
  printf "/-! # The joined top-chain glue facts of `%s`: the generated Fin's `topGlue` proof -/\n\nnamespace %s\n\n", NSN, M > f
  s = L[iTG]; sub(/^theorem topGlue : /, "theorem topGlueJ : ", s); print s > f
  joinbody(f, iTG, iLen - 1)
  printf "\nend %s\n", M > f; close(f)
  f = DIR "/LfJ.lean"
  printf "%simport %s.LfB\nimport B334.E1x.IPChk\n\n", lf, M > f; opts(f)
  printf "/-! # The joined leaf facts of `%s`: the generated Fin's `leafAll` proof -/\n\nnamespace %s\n\n", NSN, M > f
  s = L[iLeaf]; sub(/^theorem leafAll : /, "theorem leafAllJ : ", s); print s > f
  joinbody(f, iLeaf, iHLF - 1)
  printf "\nend %s\n", M > f; close(f)
  # Fin
  f = DIR "/Fin.lean"
  printf "import %s.TBJ\nimport %s.TGJ\n", M, M > f
  for (g = 0; g < ng; g++) printf "import %s.G%d\n", M, g > f
  printf "import %s.LfJ\n%s", M, keep > f
  for (i = last + 1; i < iTB; i++) print L[i] > f
  printf "/-! Joined form: `topBlk`, `topGlue`, `leafAll` and the job facts are the generated\nproofs, moved into `TBJ`, `TGJ`, `LfJ` and `G0` … `G%d`; plain `decide` is `decide +kernel` throughout. -/\n\n", ng - 1 > f
  s = L[iTB]; sub(/ := by$/, " := topBlkJ", s); printf "%s\n\n", s > f
  s = L[iTG]; sub(/ := by$/, " := topGlueJ", s); printf "%s\n\n", s > f
  for (i = iLen; i < iJobs; i++) print fixdec(L[i]) > f
  printf "%s\n  have a0 := grpJ_0\n", L[iJobs] > f
  for (g = 1; g < ng; g++) printf "  have a%d := GJ.fa_join a%d grpJ_%d\n", g, g - 1, g > f
  printf "  exact fun k hk => a%d k (Nat.zero_le k) hk\n\n", ng - 1 > f
  for (i = iEnum; i < iLeaf; i++) print fixdec(L[i]) > f
  s = L[iLeaf]; sub(/ := by$/, " := leafAllJ", s); printf "%s\n\n", s > f
  for (i = iHLF; i <= n; i++) print fixdec(L[i]) > f
  close(f)
  # layers and summary
  f = SCD "/layers.txt"
  printf "B334/E1x/%s/TBJ B334/E1x/%s/TGJ B334/E1x/%s/LfJ", NSN, NSN, NSN > f
  for (g = 0; g < ng; g++) printf " B334/E1x/%s/G%d", NSN, g > f
  printf "\nB334/E1x/%s/Fin\n", NSN > f; close(f)
  printf "%s: %d blocks (jobs 0 … %d), %d G modules (limits %d lines, %d blocks)\nlines per G:", NSN, nb, BB[nb] - 1, ng, LIM, MXB
  for (g = 0; g < ng; g++) printf " %d", GLN[g]
  printf "\nJ/K imports per G:"
  for (g = 0; g < ng; g++) printf " %d", GIM[g]
  printf "\nblocks per G:"
  for (g = 0; g < ng; g++) printf " %d", GG[g] - GF[g] + 1
  printf "\n"
}
