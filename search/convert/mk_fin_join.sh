#!/bin/bash
# mk_fin_join.sh LEANDIR NS OLDFIN WORKDIR [LIMIT] [MAXB] [OUTDIR]: the joined form of a generated multi-trace E1G Fin
# (used for R619, whose generated Fin needed 15.4 GB; the same idea as join6.py for the point S707). OLDFIN is the Fin
# written by conv_e1g_v1.py run, moved out of the tree first (LEANDIR/B334/E1x/NS/Fin.lean must be free).
# Writes into LEANDIR/B334/E1x/NS/ (refuses if a target exists; no check module is rebuilt):
#   TBJ   `topBlkJ`: the old `topBlk` proof (joins over the TB* modules);
#   TGJ   `topGlueJ`: the old `topGlue` proof (joins over TG*);
#   LfJ   `leafAllJ`: the old `leafAll` proof (joins over Lf*);
#   G<g>  the old `hjobs` blocks `have r<q> : T := P` as theorems `jrJ_<q> : T := P` (same text, dedented), at most
#         LIMIT lines (default 1500) and MAXB blocks (default 100) per module, each importing F, HT, GJ.JobS and only
#         the J/K modules its blocks name (from an index of the J/K modules' def/theorem/#e1lits names); `grpJ_<g>`
#         joins a module's blocks with GJ.fa_join;
#   Fin   topBlk/topGlue/leafAll := the joins, hjobs = the fa_join chain of the grpJ_<g>, the rest as before.
# Every plain `decide` (`:= by decide`, `; decide)`, `(by decide)`) becomes `decide +kernel`, in the blocks and in Fin.
# The stage layers (joins and G modules, then Fin) go to WORKDIR/layers.txt, with the index (WORKDIR must not exist).
# With OUTDIR (a new directory), all modules, the index and layers.txt go there instead, for comparing a regeneration
# with the modules in the tree. Needs GNU awk (gawk).
LEAN=${1:?leandir}; NS=${2:?ns}; OLD=${3:?oldfin}; WORK=${4:?workdir}; LIMIT=${5:-1500}; MAXB=${6:-100}; OUT=${7:-}
D=$LEAN/B334/E1x/$NS
[ -f "$OLD" ] || { echo "no $OLD"; exit 2; }
[ -d "$D" ] || { echo "no $D"; exit 2; }
if [ -z "$OUT" ]; then
  O=$D; SC=$WORK
  for f in Fin TBJ TGJ LfJ; do [ -e "$O/$f.lean" ] && { echo "exists: $O/$f.lean"; exit 1; }; done
  [ -z "$(ls "$O" | awk '/^G[0-9]+\.lean$/')" ] || { echo "G modules exist in $O"; exit 1; }
else
  O=$OUT; SC=$OUT
fi
[ -e "$SC" ] && { echo "exists: $SC"; exit 1; }
NJ=$(awk '/^def nJ : Nat := /{print $6}' "$D/HT.lean")
[ -n "$NJ" ] || { echo "no nJ in $D/HT.lean"; exit 2; }
FILES=$(cd "$D" && ls | awk '/^(J[0-9]+|K[0-9]+L|K[0-9]+C[0-9]+)\.lean$/')
[ -n "$FILES" ] || { echo "no J/K modules in $D"; exit 2; }
mkdir -p "$SC" || exit 3
(cd "$D" && awk -v NSN="$NS" 'FNR == 1 { m = FILENAME; sub(/\.lean$/, "", m) }
  /^def (JL|JW|KW)_[0-9]+ / { print $2, m }
  /^theorem (jr|kb|kg)_[0-9_]+ / { print $2, m }
  /^#e1lits / { s = $2; sub("^B334[.]E1x[.]" NSN "[.]", "", s); print s ".lits", m }' $FILES) > "$SC/index.txt" || exit 3
gawk -v NSN="$NS" -v LIM="$LIMIT" -v MXB="$MAXB" -v NJV="$NJ" -v DIR="$O" -v SCD="$SC" \
  -f "$(dirname "$0")/mk_fin_join.awk" "$SC/index.txt" "$OLD" || exit 4
left=$(command grep -l 'decide$\|decide)' "$O/Fin.lean" "$O/TBJ.lean" "$O/TGJ.lean" "$O/LfJ.lean" "$O"/G[0-9]*.lean)
[ -z "$left" ] || { echo "plain decide left in: $left"; exit 5; }
echo "index $(awk 'END{print NR}' "$SC/index.txt") names; Fin $(awk 'END{print NR}' "$O/Fin.lean") lines; output in $O"
