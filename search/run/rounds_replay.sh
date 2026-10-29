#!/bin/bash
# rounds_replay.sh BIN C [THREADS] : the replay of all traces of a run of rounds_search.sh by lechk9vr (lechk9m4 with
# CHK=lechk9m4); it must end with "RESULT PASS" and coverage COMPLETE. IP from IPF (default ip_P<C>_seeded_L25.txt).
BIN=${1:?bin}; C=${2:?name}; TH=${3:-16}
mkdir -p logs; touch leaves_P${C}.txt
$BIN/${CHK:-lechk9vr} ${IPF:-ip_P${C}_seeded_L25.txt} --threads $TH --sols leaves_P${C}.txt t/P${C}_*.bin > logs/replay_P${C}.txt 2>&1
tail -6 logs/replay_P${C}.txt
