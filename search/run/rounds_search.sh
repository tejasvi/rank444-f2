#!/bin/bash
# rounds_search.sh BIN C [THREADS] [BUDGET] : the traced search in rounds, as the two point searches (paper, Section 4)
# and the searches of the heaviest raised planes ran it. BIN: the directory of the built programs; C: the run name
# (file names use P<C>, e.g. C = 707R2b); THREADS (176) and BUDGET (node budget per job, 30000) as in the original runs.
# Pass 1 runs the search with --frontier 3 in jobs; a job that visits more than BUDGET nodes is abandoned and its prefix
# written to a heavy file. Round n >= 1 takes the sorted union of the heavy files of round n-1 (roots_P<C>_r<n>.txt),
# splits it once into chunks (line i -> chunk (i-1) mod P; P stored in roots_P<C>_r<n>.chunks) and runs each chunk as a
# separate process with --roots ... RELD; the rounds go on until no job is abandoned. Only who runs which subtree
# changes from one round to the next; together the rounds cover the search tree once.
# Files, in the current directory: st_P<C>_r*.txt (job states), heavy_P<C>_r*.txt, t/P<C>_r<n>[_c<k>]_*.bin (traces),
# leaves_P<C>.txt, logs/. Resumable: a chunk with a .done file is skipped; the others resume from their state files.
# Environment: IPF (IP file, default ip_P<C>_seeded_L25.txt), LPMAX (24 = L - 1), RPC (roots per chunk, 16), MAXCH (most
# chunks per round, 22), RELD (2), ENUM (the enumerator, lineenum9vr; lineenum9m4 for IPs with label caps of 4).
BIN=${1:?bin}; C=${2:?name}; TH=${3:-176}; B=${4:-30000}
mkdir -p t logs
fix_tail(){ f=$1; [ -s "$f" ] || return 0; if [ "$(tail -c1 "$f" | od -An -tx1 | tr -d ' ')" != "0a" ]; then head -n -1 "$f" > "$f.tmp" && mv "$f.tmp" "$f" && echo "$(date -u +%FT%TZ) dropped a partial last line of $f"; fi; }
for f in st_P${C}_r*.txt heavy_P${C}_r*.txt leaves_P${C}.txt; do [ -e "$f" ] && fix_tail "$f"; done
IP=${IPF:-ip_P${C}_seeded_L25.txt}; LPMAX=${LPMAX:-24}; RPC=${RPC:-16}; MAXCH=${MAXCH:-22}; RELD=${RELD:-2}
BASE="--lp 1 $LPMAX --sepmode 1 --inherit 0 --lpadd 50 --seed 1 --budget $B"
if ! [ -s logs/P${C}_r0.done ]; then
  echo "$(date -u +%FT%TZ) start/resume pass 1 (budget $B)" >> logs/P${C}_r0.log
  $BIN/${ENUM:-lineenum9vr} $IP $BASE --threads $TH --frontier 3 --state st_P${C}_r0.txt --cert t/P${C}_r0 --out leaves_P${C}.txt --heavy heavy_P${C}_r0.txt >> logs/P${C}_r0.log 2>&1
  rc=$?; if [ $rc -ne 0 ]; then echo "pass 1 rc=$rc"; exit $rc; fi
  grep 'FINAL' logs/P${C}_r0.log | tail -1 > logs/P${C}_r0.done
fi
n=1; prevh="heavy_P${C}_r0.txt"
while true; do
  R=roots_P${C}_r$n.txt
  if ! [ -e "$R" ]; then cat $prevh 2>/dev/null | sort -u > "$R.tmp" && mv "$R.tmp" "$R"; fi
  [ -s "$R" ] || break
  if ! [ -s "roots_P${C}_r$n.chunks" ]; then
    nr=$(wc -l < "$R"); P=$(( (nr + RPC - 1) / RPC )); [ $P -gt $MAXCH ] && P=$MAXCH; [ $P -lt 1 ] && P=1
    awk -v P=$P -v pre="roots_P${C}_r${n}_c" '{ f = pre ((NR-1) % P) ".txt"; print > f }' "$R"
    echo $P > "roots_P${C}_r$n.chunks"
  fi
  P=$(cat "roots_P${C}_r$n.chunks"); T=$(( (TH * 3 / 2 + P - 1) / P )); [ $T -lt 1 ] && T=1; [ $T -gt $TH ] && T=$TH
  echo "$(date -u +%FT%TZ) heavy round $n: $(wc -l < "$R") roots in $P chunks, $T threads each, budget $B"
  for k in $(seq 0 $((P-1))); do
    if ! [ -s logs/P${C}_r${n}_c$k.done ]; then
      ( echo "$(date -u +%FT%TZ) start/resume round $n chunk $k ($(wc -l < roots_P${C}_r${n}_c$k.txt) roots, $T threads, budget $B)" >> logs/P${C}_r${n}_c$k.log
        $BIN/${ENUM:-lineenum9vr} $IP $BASE --threads $T --roots roots_P${C}_r${n}_c$k.txt $RELD --state st_P${C}_r${n}_c$k.txt --cert t/P${C}_r${n}_c$k --out leaves_P${C}.txt --heavy heavy_P${C}_r${n}_c$k.txt >> logs/P${C}_r${n}_c$k.log 2>&1
        rc=$?; if [ $rc -eq 0 ]; then grep 'FINAL' logs/P${C}_r${n}_c$k.log | tail -1 > logs/P${C}_r${n}_c$k.done; fi ) &
    fi
  done
  wait
  bad=0; for k in $(seq 0 $((P-1))); do [ -s logs/P${C}_r${n}_c$k.done ] || { echo "round $n chunk $k did not finish"; bad=1; }; done
  [ $bad -eq 0 ] || exit 5
  prevh="heavy_P${C}_r${n}_c*.txt"; n=$((n+1))
done
echo "CLASS $C ENUMERATION DONE: $(cat st_P${C}_r*.txt | awk '{n+=$2; l+=$3; c++} END{print c" jobs, "n" nodes, "l" leaves"}')"
