#!/bin/bash
# rounds_complete.sh BIN C TARGET LAB2COS : completes or refutes every leaf of a run of rounds_search.sh with tsolve334
# (time limits 60 s, then 600 s, then 3600 s). TARGET: T mod E in reduced coordinates (lines "x y z"); LAB2COS: the
# label -> coset map of the IP (s4_labmaps.py). Exit 9 = a SAT leaf (a decomposition); 8 = leaves left undecided after
# 3600 s; 0 = every leaf refuted, or no leaves.
BIN=${1:?bin}; C=${2:?name}; T=${3:?target}; MAP=${4:?lab2cos}
mkdir -p logs
[ -s leaves_P${C}.txt ] || { echo "class $C: no leaves"; exit 0; }
awk 'NR==FNR{m[$1]=$2; next} {s=""; for(i=1;i<=NF;i++) s=s" "m[$i]; print "leaf" FNR ":" s}' "$MAP" leaves_P${C}.txt > inst_P${C}_0.a
lim=(60 600 3600); prev=inst_P${C}_0.a
for k in 0 1 2; do
  $BIN/tsolve334 --target $T --timelimit ${lim[$k]} $prev > logs/ts_P${C}_$k.txt 2> logs/ts_P${C}_$k.err
  echo "class $C limit ${lim[$k]} s: UNSAT $(grep -c '^UNSAT' logs/ts_P${C}_$k.txt) ABORT $(grep -c '^ABORT' logs/ts_P${C}_$k.txt) SAT $(grep -c '^SAT' logs/ts_P${C}_$k.txt)"
  if grep -q '^SAT' logs/ts_P${C}_$k.txt; then echo "SAT FOUND for class $C"; exit 9; fi
  grep '^ABORT' logs/ts_P${C}_$k.txt | awk -F'|' '{sub(/^ABORT /,"",$1); print $1}' > inst_P${C}_$((k+1)).a
  if ! [ -s inst_P${C}_$((k+1)).a ]; then echo "class $C: all leaves refuted"; exit 0; fi
  prev=inst_P${C}_$((k+1)).a
done
echo "class $C: $(wc -l < $prev) leaves still ABORT after 3600 s"; exit 8
