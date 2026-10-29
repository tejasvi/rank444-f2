#!/bin/bash
# release_build_v3.sh RUN (the reference build): the clean release build, with the sources taken from b334/rel3src,
# the lists from b334/release/rel3/, and the build
# driver od1pkg/leanL_build_v3.sh, which gives the modules under B334/E1x/Pts/S707/ and B334/Main -M MEMMB_HI (default
# 18000) from the start and every other module -M MEMMB (default 15000). In detail:
# the CLEAN release build of the B334 tree in a fresh dir on the box's data disk, from sources and data only (no seeded
# oleans). Inputs on the control host, in b334/release/rel3/:
#   MODULES.txt     module<TAB>kind<TAB>sha256_16: the release modules (Main's import closure, the censuses);
#   layers.txt      one layer per line, modules separated by spaces (import order), covering exactly MODULES.txt;
#   DATA_FILES.tsv  path<TAB>bytes<TAB>sha256<TAB>source<TAB>... : every data file the modules read, `path` relative to
#                   lean/ (e.g. ../data/j0.bin, ../runs/gensim3/x.bin), `source` the box lean dir it was read from.
# Steps: refuse if b334run26/RUN exists, the root disk is at 90% or more, or the data disk has under 100 GB free;
# make ~/gsl/b334blocks/RUN/L (symlinked as b334run26/RUN); ship the sources by tar and verify them with sha256sum -c
# (snapshot written on the control host just before); copy every data file from its source and verify the whole data set
# against DATA_FILES.tsv's sha256; then the build with PAR, MEMMB, MEMMB_HI, TMO (defaults 38, 15000, 18000, 6000) and
# KEEPGOING=1. Nothing in the source tree or in dev1 is touched.
RUN=${1:?run}; B=<build>/mm4/next/b334; P=$B/release/rel3; S=$B/rel3src; BD=<build>/b334run26
GR=<build>/gsl/b334blocks; SSH="bash <build>/mm4/lean/tools/vm/ssh.sh <box>"
PAR=${PAR:-38}; MEMMB=${MEMMB:-15000}; MEMMB_HI=${MEMMB_HI:-18000}; TMO=${TMO:-6000}
for f in MODULES.txt layers.txt DATA_FILES.tsv; do [ -s $P/$f ] || { echo "need $P/$f"; exit 2; }; done
nm=$(awk -F'\t' 'NF{print $1}' $P/MODULES.txt | sort -u | wc -l); nl=$(tr ' ' '\n' < $P/layers.txt | awk 'NF' | sort -u | wc -l)
[ "$nm" = "$nl" ] || { echo "layers.txt covers $nl modules, MODULES.txt lists $nm: refusing"; exit 2; }
timeout 60 $SSH "rp=\$(df --output=pcent <build> | tail -1 | tr -dc 0-9); ga=\$(df -B1 --output=avail $GR | tail -1 | tr -dc 0-9); echo \"root \$rp%, data disk avail \$((ga/1000000000)) GB\"; [ \"\$rp\" -lt 90 ] && [ \"\$ga\" -gt 100000000000 ] && [ ! -e $BD/$RUN ] && mkdir -p $GR/$RUN/L && ln -s $GR/$RUN $BD/$RUN" < /dev/null || { echo "disk/dir check failed: refusing"; exit 3; }
awk -F'\t' 'NF{print "lean/" $1 ".lean"}' $P/MODULES.txt > $P/files_$RUN.txt
(cd $S && xargs -a $P/files_$RUN.txt -d '\n' sha256sum) > $P/snapshot_$RUN.sha256 || { echo "snapshot failed"; exit 4; }
[ "$(wc -l < $P/snapshot_$RUN.sha256)" = "$nm" ] || { echo "snapshot has the wrong length"; exit 4; }
(cd $S && tar -cf - -T $P/files_$RUN.txt) | timeout 1800 $SSH "tar -C $BD/$RUN/L -xf -" || { echo "tar failed"; exit 5; }
timeout 600 $SSH "cd $BD/$RUN/L && cat > snapshot.sha256 && sha256sum -c --quiet snapshot.sha256 && echo \"sources verified: \$(wc -l < snapshot.sha256)\"" < $P/snapshot_$RUN.sha256 || { echo "source verify failed"; exit 6; }
awk -F'\t' 'NR>1 && NF {print $4 "/" $1 "\t" $1}' $P/DATA_FILES.tsv | timeout 3600 $SSH "cd $BD/$RUN/L/lean && n=0; while IFS=\$'\t' read -r src rel; do mkdir -p \$(dirname \"\$rel\") && cp -p \"\$src\" \"\$rel\" && n=\$((n+1)); done; echo data copied: \$n" || { echo "data copy failed"; exit 7; }
awk -F'\t' 'NR>1 && NF {print $3 "  " $1}' $P/DATA_FILES.tsv | timeout 3600 $SSH "cd $BD/$RUN/L/lean && cat > ../data_sha256.txt && sha256sum -c --quiet ../data_sha256.txt && echo \"data verified: \$(wc -l < ../data_sha256.txt)\"" || { echo "data verify failed"; exit 8; }
timeout 60 $SSH "cat > $BD/$RUN/L/layers.txt" < $P/layers.txt || exit 9
timeout 60 $SSH "cat > $BD/$RUN/L/leanL_build.sh" < $B/od1pkg/leanL_build_v3.sh || exit 9
timeout 60 $SSH "cd $BD/$RUN/L && (PAR=$PAR MEMMB=$MEMMB MEMMB_HI=$MEMMB_HI TMO=$TMO KEEPGOING=1 setsid nohup nice -n 5 bash leanL_build.sh $BD/$RUN/L > leanL.out 2>&1 < /dev/null &); sleep 5; cat leanL.pid; head -2 STATUS.txt" < /dev/null
