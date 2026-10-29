#!/bin/bash
# leanL_build_v3.sh RUN_DIR (runs on the build box; the driver of the reference build): leanL_build.sh with a second
# memory limit. The modules under B334/E1x/Pts/S707/ and B334/Main get -M MEMMB_HI (MB); every other module gets
# -M MEMMB. Otherwise unchanged:
# build B334 Lean modules in dependency layers with Lean v4.30.0 against the staged Mathlib v4.30.0
# (b334run26/leanenv430; read only, LEAN_PATH; no lake, no git).
# RUN_DIR holds lean/ (the B334 tree) and layers.txt: one line per layer, modules separated by spaces (e.g.
# "B334/MethodK/Rows/R6D B334/MethodK/Rows/R12D").  The modules of a layer build in parallel (at most PAR at a time);
# layers run in order.  Per process: -j1, -M (MB), timeout TMO s; /usr/bin/time records wall, user and maxrss.
# Results: times.txt (one line per module), STATUS.txt, logs/; DONE at the end.  STOP file: start nothing new.
W=${1:?run dir}; E=<build>/b334run26/leanenv430
PAR=${PAR:-60}; MEMMB=${MEMMB:-12000}; MEMMB_HI=${MEMMB_HI:-$MEMMB}; TMO=${TMO:-3000}
cd $W/lean || exit 1; echo $$ > $W/leanL.pid
LEAN=$E/toolchain/bin/lean
LP=$W/lean/.build; for d in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient; do LP="$LP:$E/pkgs/$d/lean"; done
export LEAN_PATH=$LP
mkdir -p $W/logs
log(){ echo "$(date -u +%FT%TZ) $*" >> $W/STATUS.txt; }
build(){ m=$1; mkdir -p .build/$(dirname $m); lg=$W/logs/$(echo $m | tr / _).log
  [ -e $W/STOP ] && return 1
  mm=$MEMMB; case $m in B334/E1x/Pts/S707/*|B334/Main) mm=$MEMMB_HI;; esac
  /usr/bin/time -f '%e s wall %U s user %M KB maxrss' -o $lg.time timeout $TMO $LEAN -j1 -M $mm --root=. -o .build/$m.olean $m.lean > $lg 2>&1; rc=$?
  echo "$m rc=$rc $(tail -1 $lg.time 2>/dev/null) errors=$(grep -c 'error' $lg) M=$mm" >> $W/times.txt; return $rc; }
log "leanL start (pid $$, PAR $PAR, MEMMB $MEMMB, MEMMB_HI $MEMMB_HI for B334/E1x/Pts/S707/* and B334/Main, $(wc -l < $W/layers.txt) layers, lean $($LEAN --version | head -1))"
n=0; fail=0
while read -r layer; do n=$((n+1)); [ -z "$layer" ] && continue
  [ -e $W/STOP ] && { log "STOP present: exit before layer $n"; break; }
  log "layer $n: $(echo $layer | wc -w) modules"
  pids=""; k=0
  for m in $layer; do build $m & pids="$pids $!"; k=$((k+1)); if [ $k -ge $PAR ]; then wait -n; k=$((k-1)); fi; done
  for p in $pids; do wait $p || fail=1; done
  if [ $fail = 1 ] && [ "${KEEPGOING:-0}" != 1 ]; then log "layer $n: a module FAILED (times.txt); stopping"; break; fi
  [ $fail = 1 ] && log "layer $n: failures recorded (KEEPGOING=1: mutant block, continuing)"
done < $W/layers.txt
log "leanL DONE (fail=$fail): $(grep -c 'rc=0' $W/times.txt) modules ok, $(grep -vc 'rc=0' $W/times.txt) failed; max maxrss $(awk '{for(i=1;i<=NF;i++) if($i=="KB") print $(i-1)}' $W/times.txt | sort -n | tail -1) KB"
touch $W/DONE
