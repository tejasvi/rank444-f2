#!/bin/bash
# fidelity_check.sh TAG MODULE... (the fidelity gate): elaborate the given B334 modules with
# autoImplicit and relaxedAutoImplicit OFF, in a scratch copy on the box's data disk, against dev1's oleans; nothing in
# dev1 or the source tree is edited or overwritten. MODULE paths are relative to b334/lean (e.g. B334/Statement). The
# sources come from the control host's b334/lean (pushed fresh), the outputs go to ~/gsl/b334blocks/fid_TAG/.build.
# Prints one line per module (rc, wall, maxrss, errors) and the first 40 log lines of a failing module.
TAG=${1:?tag}; shift
B=<build>/mm4/next/b334; G=<build>/gsl/b334blocks/fid_$TAG
SSH="bash <build>/mm4/lean/tools/vm/ssh.sh <box>"
[ $# -gt 0 ] || { echo "no modules"; exit 2; }
# Lean resolves a package directory (B334/) in the first LEAN_PATH entry that has it, so the scratch tree gets its own
# copy of dev1's oleans (no layering); outputs then replace only the scratch copies.
timeout 60 $SSH "[ -e $G ] && { echo '$G exists: refusing'; exit 1; }; mkdir -p $G/lean $G/logs" < /dev/null || exit 3
# OLEANS_FROM (env, default the dev1 tree): the lean dir whose .build is copied, e.g. the release tree
# <build>/b334run26/rel1/L/lean for the release fidelity gate.
OF=${OLEANS_FROM:-<build>/b334run26/dev1/lean}
timeout 3600 $SSH "cp -a $OF/.build $G/lean/.build && echo 'oleans copied from $OF'" < /dev/null || exit 3
# SRC (env, default b334/lean): the source root on the control host, e.g. the release source tree.
S=${SRC:-$B/lean}
for m in "$@"; do [ -f $S/$m.lean ] || { echo "no file $S/$m.lean"; exit 2; }
  timeout 60 $SSH "mkdir -p $G/lean/\$(dirname $m) && cat > $G/lean/$m.lean" < $S/$m.lean || exit 4; done
timeout 7200 $SSH "E=<build>/b334run26/leanenv430; cd $G/lean || exit 1
LP=$G/lean/.build; for d in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient; do LP=\"\$LP:\$E/pkgs/\$d/lean\"; done
export LEAN_PATH=\$LP; rc=0
for m in $*; do mkdir -p .build/\$(dirname \$m); lg=$G/logs/\$(echo \$m | tr / _).log
  /usr/bin/time -f '%e s wall %M KB maxrss' -o \$lg.time timeout 6000 \$E/toolchain/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false -j1 -M 15000 --root=. -o .build/\$m.olean \$m.lean > \$lg 2>&1; r=\$?
  echo \"\$m rc=\$r \$(tail -1 \$lg.time) errors=\$(grep -c 'error' \$lg)\"; [ \$r = 0 ] || { rc=1; head -40 \$lg; }; done; exit \$rc" < /dev/null
