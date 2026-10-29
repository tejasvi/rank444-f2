#!/bin/bash
# table_class.sh BIN TABLE SCHEME C L : one search of the class table (paper, Section 5), as the table searches ran it.
#   BIN     the directory of the built programs (build.sh); TABLE seeded334.tsv; SCHEME a rank-29 scheme of <3,3,4>
#           (used by mkcompS9 only for its positive control); C the class; L the search length (the class's seeded lb
#           minus 1 for the searches that confirm a seeded value).
# Steps, in the current directory (subdirectories ip/ tr/ lv/ comp/ logs/ res/):
#   1. the IP ip/ipS_c<C>_L<L>.txt by mkipS9 --maxgroup 2048 (exit 3 = MONOTONE: a strict superspace already has
#      lb > L, so no search is needed);
#   2. the traced search with lineenum9vr, lineenum9m4 or lineenum9m8, chosen by the IP's largest label cap (<= 3, 4, 8),
#      with the options of the table searches; traces tr/c<C>_L<L>_<pid>_*.bin, leaves lv/leaves_c<C>.txt;
#   3. the replay with the matching lechk9 (it must print "RESULT PASS" and "coverage: COMPLETE");
#   4. if there are leaves: the leaf questions by mkcompS9 and their completion by tsolve334 (time limits 60 s, then
#      600 s for the leaves left; CPAR parallel parts). A SAT leaf (a decomposition) stops with exit 9.
# The result line goes to res/rb_c<C>.done (or .fail / .timeout). Environment: SECS (search time limit, 1800),
# CPAR (4), SIBK (4; empty: no --sibk option, as in the searches of the raised lines and planes).
BIN=${1:?bin}; TAB=${2:?table}; SCH=${3:?scheme}; c=${4:?class}; L=${5:?length}
SECS=${SECS:-1800}; CPAR=${CPAR:-4}; SIBK=${SIBK-4}
mkdir -p ip tr lv comp logs res
enum_for(){ awk '$1=="C" && $4==1 {if($3>m) m=$3} END{m+=0; if(m<=3) print "vr"; else if(m<=4) print "m4"; else if(m<=8) print "m8"; else print "none"}' $1; }
complete1(){ c=$1; n=$(wc -l < comp/inst_c$c.a); [ "$n" -eq 0 ] && { echo "leaves 0"; return 0; }
  local in=comp/inst_c$c.a sumU=0 sumA=0 lim pre
  for lim in 60 600; do [ -s "$in" ] || break
    pre=comp/part_c${c}_L${lim}_$(date +%s)_
    split -n l/$CPAR -d -a 3 "$in" $pre
    for f in ${pre}[0-9][0-9][0-9]; do [ -s "$f" ] || continue; ( $BIN/tsolve334 --timelimit $lim --target comp/qS_c$c.t "$f" > "$f.res" 2>/dev/null ) & done; wait
    cat ${pre}[0-9][0-9][0-9].res > comp/res${lim}_c$c.txt 2>/dev/null
    u=$(grep -c '^UNSAT' comp/res${lim}_c$c.txt); a=$(grep -c '^ABORT' comp/res${lim}_c$c.txt); s=$(grep -c '^SAT' comp/res${lim}_c$c.txt)
    sumU=$((sumU+u))
    if [ "$s" -gt 0 ]; then echo "SAT $s"; return 9; fi
    sed -n 's/^ABORT \([^|]*\)|.*/\1/p' comp/res${lim}_c$c.txt > comp/ab${lim}_c$c.a; in=comp/ab${lim}_c$c.a; sumA=$a
  done
  echo "leaves $n: UNSAT $sumU ABORT_left $sumA"; [ "$sumA" -eq 0 ]; }
ip=ip/ipS_c${c}_L$L.txt; t0=$(date +%s)
if [ ! -s $ip ]; then $BIN/mkipS9 $TAB $c $L $ip --maxgroup 2048 > logs/mkip_c$c.out 2>&1; rc=$?
  if [ $rc -eq 3 ]; then echo "$c L=$L MONOTONE (a strict superspace already has lb > L)" > res/rb_c$c.done; cat res/rb_c$c.done; exit 0; fi
  [ $rc -ne 0 ] && { echo "$c L=$L mkipS9 rc=$rc" > res/rb_c$c.fail; cat res/rb_c$c.fail; exit 1; }; fi
e=$(enum_for $ip)
if [ "$e" = none ]; then echo "$c L=$L label cap > 8: no enumerator variant" > res/rb_c$c.fail; cat res/rb_c$c.fail; exit 1; fi
: > lv/leaves_c$c.txt
r=$(timeout $SECS $BIN/lineenum9$e $ip --lp 1 $((L-1)) --sepmode 1 --inherit 0 --lpadd 50 ${SIBK:+--sibk $SIBK} --cert tr/c${c}_L$L --out lv/leaves_c$c.txt 2>&1 | grep -E '^DONE|unsupported' | tr '\n' ' ')
if [ -z "$r" ]; then echo "$c L=$L TIMEOUT ${SECS}s ($e)" > res/rb_c$c.timeout; cat res/rb_c$c.timeout; exit 1; fi
$BIN/lechk9$e $ip --sols lv/leaves_c$c.txt tr/c${c}_L${L}_*.bin > logs/replay_c$c.txt 2>&1
rp=FAIL; grep -q 'RESULT PASS' logs/replay_c$c.txt && grep -q 'coverage: COMPLETE' logs/replay_c$c.txt && rp="PASS COMPLETE"
nl=$(sed -n 's/^leaves: \([0-9]*\) distinct.*/\1/p' logs/replay_c$c.txt | tail -1)
if [ "$rp" != "PASS COMPLETE" ]; then echo "$c L=$L $e search[$r] replay FAIL" > res/rb_c$c.fail; cat res/rb_c$c.fail; exit 1; fi
cr="leaves 0"
if [ "${nl:-0}" -gt 0 ]; then
  $BIN/mkcompS9 $TAB $SCH comp lv $c > logs/mkcomp_c$c.out 2>&1 || { echo "$c L=$L mkcompS9 failed" > res/rb_c$c.fail; exit 1; }
  cr=$(complete1 $c); [ $? -eq 9 ] && { echo "$c L=$L SAT leaf: $cr" > res/rb_c$c.fail; exit 9; }; fi
echo "$c L=$L $e grp[$(grep -o '|Stab|=[^;]*' logs/mkip_c$c.out | head -1)] search[$r] replay[$rp] leaves[${nl:-0}] completion[$cr] secs[$(( $(date +%s) - t0 ))]" > res/rb_c$c.done
cat res/rb_c$c.done
