#!/bin/bash
# build.sh OUTDIR HIGHS_LIBDIR [MARCH] : compiles the C++ programs into OUTDIR (a new or empty directory).
#   HIGHS_LIBDIR  a directory with libhighs.so.1, the HiGHS library of the Python wheel highspy 1.15.1 (MIT license;
#                 after `pip install highspy==1.15.1` it is the package directory site-packages/highspy). It is copied
#                 into OUTDIR; the search programs lineenum9vr, lineenum9m4 and lineenum9m8 link it and find it there
#                 (rpath $ORIGIN), so OUTDIR can be moved to another machine as a whole.
#   MARCH         the value of -march (default native) for all programs but gen7_334, chk334c and chk334e, which are
#                 built without -march; the builds that made the original runs of those nine programs used znver4, and
#                 the original build scripts of the other three add no -march by default.
# Flags: -O3 for the search and replay programs and -O2 for the others, as in the original builds; -std=c++17 (tsolve334:
# the compiler's default standard). The C++ runtime is linked statically into every program; the builds that made the
# original runs did so for the nine programs that take MARCH.
OUT=${1:?outdir}; H=${2:?highs libdir}; MARCH=${3:-native}
D=$(cd "$(dirname "$0")" && pwd)
[ -f "$H/libhighs.so.1" ] || { echo "no libhighs.so.1 in $H"; exit 2; }
mkdir -p "$OUT" || exit 2
[ -z "$(ls -A "$OUT")" ] || { echo "$OUT is not empty"; exit 2; }
cp "$H/libhighs.so.1" "$OUT/" || exit 2
ST="-static-libstdc++ -static-libgcc"
set -x
for e in vr m4 m8; do
  g++ -O3 -march=$MARCH -std=c++17 -pthread "$D/enum/lineenum9$e.cc" -o "$OUT/lineenum9$e" -L"$OUT" -l:libhighs.so.1 -Wl,-rpath,'$ORIGIN' $ST || exit 3
  g++ -O3 -march=$MARCH -std=c++17 -pthread "$D/enum/lechk9$e.cc" -o "$OUT/lechk9$e" $ST || exit 3
done
g++ -O2 -march=$MARCH -std=c++17 "$D/ip/mkipS9.cc" -o "$OUT/mkipS9" $ST || exit 3
g++ -O2 -march=$MARCH -std=c++17 "$D/leaves/mkcompS9.cc" -o "$OUT/mkcompS9" $ST || exit 3
g++ -O2 -march=$MARCH "$D/leaves/tsolve334.cc" -o "$OUT/tsolve334" $ST || exit 3
g++ -O2 -std=c++17 -Wall -Wno-unused-function "$D/leaves/gen7_334.cc" -o "$OUT/gen7_334" $ST || exit 3
g++ -O2 -std=c++17 -Wall -Wextra "$D/check/chk334c.cc" -o "$OUT/chk334c" $ST || exit 3
g++ -O2 -std=c++17 -Wall -Wextra "$D/check/chk334e.cc" -o "$OUT/chk334e" $ST || exit 3
set +x
echo "built: $(ls "$OUT" | tr '\n' ' ')"
