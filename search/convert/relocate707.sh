#!/bin/bash
# relocate707.sh DATA707SRC DATA708 S707DIR OUTDIR : the last step of the S707 modules. The data files of the two point
# runs share one directory data/ in the release, but some names occur in both runs (j<k>.bin, k<k>.bin, ht.bin, top*.bin).
# The S707 files with such names go to data707/, and the S707 modules that read them read "../data707/<f>" instead of
# "../data/<f>". This step was done by hand for the release; this script repeats it.
#   DATA707SRC  the data/ directory written for S707 (conv_e1p.py run);  DATA708  the same for S708;
#   S707DIR     the directory of the S707 modules (lean/B334/E1x/Pts/S707 of the S707 stage);
#   OUTDIR      a new directory: OUTDIR/data707/ gets copies of the S707 files whose names occur in DATA708, and
#               OUTDIR/S707/ copies of all S707 modules, with the paths changed in the modules that read those files.
A=${1:?data707src}; B=${2:?data708}; M=${3:?s707dir}; O=${4:?outdir}
[ -d "$A" ] && [ -d "$B" ] && [ -d "$M" ] || { echo "missing input directory"; exit 2; }
[ -e "$O" ] && { echo "exists: $O"; exit 2; }
mkdir -p "$O/data707" "$O/S707" || exit 3
(cd "$A" && ls) | LC_ALL=C sort > "$O/names707.txt"; (cd "$B" && ls) | LC_ALL=C sort > "$O/names708.txt"
LC_ALL=C comm -12 "$O/names707.txt" "$O/names708.txt" > "$O/clash.txt"
while read -r f; do cp -p "$A/$f" "$O/data707/$f" || exit 4; done < "$O/clash.txt"
n=0
for p in "$M"/*.lean; do
  q="$O/S707/$(basename "$p")"
  awk 'NR == FNR { c["\"../data/" $0 "\""] = "\"../data707/" $0 "\""; next }
       { for (k in c) if (index($0, k)) { i = index($0, k); $0 = substr($0, 1, i - 1) c[k] substr($0, i + length(k)) } print }' \
    "$O/clash.txt" "$p" > "$q" || exit 5
  cmp -s "$p" "$q" || n=$((n+1))
done
echo "relocate707: $(wc -l < "$O/clash.txt") data files to data707/, $n modules changed"
