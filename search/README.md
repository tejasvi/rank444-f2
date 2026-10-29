# B334 search programs

This directory holds the programs used for the computations in T. S. Tomar, *The rank of 4×4 matrix multiplication
over F₂ is at least 35* (doi:10.5281/zenodo.23749576). The same programs wrote the data files and the generated Lean
modules of this archive.

The Lean proof does not depend on these programs being correct: Lean replays the recorded searches and checks the
certificates and the class table (the top-level `README.md` describes the trust base). The programs document how each
file was made, and they let you rerun the searches.

## Terms

The notation is that of the paper (Sections 2 and 4). T is the tensor ⟨3,3,4⟩, A the space of the first factors of
its decompositions, and E a subspace of A. E is a *point* if its dimension is 1, as in the paper; this README calls
it a *line* or a *plane* if its dimension is 2 or 3. For a subspace S of A, lb(S) is a proved lower bound on the
number of terms whose first factor lies outside S. The two *point searches* are those for E = span(v2) and
E = span(v3); files and modules name them by their class numbers, 707 for span(v2) (run name `707R2b`, modules `S707`
and `H707`, target `q10.t`) and 708 for span(v3) (`708R2`, `S708`, `H708`, `q84.t`). The third point class, 706,
occurs only in some file names.

- The *profile* of a decomposition is the multiset of the cosets a + E of its first factors a ∉ E. A search fixes E
  and a length L and enumerates the possible profiles with L elements. When its trace covers the whole search tree and
  every leaf is refuted, it proves that every decomposition has at least L + 1 terms whose first factor lies outside E
  (Section 4 explains why profiles of exactly L elements suffice).
- A search reads an *IP file*, or *IP* for short (named `ip_…` or `ipS_…`). It lists the nonzero cosets
  of E (the *labels*), the *cap* L − lb(S) of each strict superspace S of E (at most that many profile elements lie
  in S), and the symmetry group. The *label cap* of a label a is the cap of E + ⟨a⟩, which bounds how often a may
  occur. The three variants of the search handle label caps up to 3, 4 and 8.
- G₀ splits the subspaces of A into 710 orbits, the *classes*. The class table has one row for each class, with its
  bound and the *argument* that proves it (Section 5). The *seeded bound* of a class S, the table's starting value, is
  the larger of the bound in Wang's table (Section 5) and b + g, where b is the bound of the ⟨3,3,3⟩ class of S and
  g ≤ 3 is a gain computed from S (`seed334.py` gives the formula). The searches confirmed the seeded bounds or raised
  them; the *raised* lines and planes are those whose bound is now above the seeded one. The *backtracking rows* are
  the classes that Wang's table settles by backtracking, and the *lifted rows* the classes with an entry in the column
  `lift_L` of `inputs/table_v2.tsv`, whose seeded bound comes from the ⟨3,3,3⟩ class and is above Wang's.
- The proof trace of a search is made of *blocks*; a one-thread search writes a single block. A search *in rounds*
  splits the tree into *jobs* with a budget of 30,000 nodes. A first pass runs every job. Each round takes the jobs
  that ran out of budget (its *roots*), splits them into smaller ones and reruns them, in *chunks* that run as separate
  processes; the rounds go on until no job runs out of budget. Each job writes one block, and the tree above the jobs
  is written as further blocks.
- A *leaf* is a profile that meets every cap; its *leaf question* asks whether T mod E has a decomposition with that
  profile. `tsolve334` decides leaf questions, and `gen7_334` writes the certificate that refutes one. The *positive
  control* `pos_c<c>.a` is a leaf question that has a solution, made from a known decomposition of rank 29.
- The *axiom gate* `Ax` of a run checks that its main theorems use only the standard axioms; four runs also allow the
  axiom of the `native_decide` check in `B334/T2/N_0` (step 5). *Mutants* are altered blocks or certificates. The
  *test target* is the separate Lean target `lean_tests/` of this archive. Its modules are negative controls: each
  numbered module `Neg<k>` gives a Lean checker a mutant loaded by its run's `NegL` module (`I692/Neg`, which has no
  `NegL`, carries its own) and checks that the checker rejects it, and `AxCheckT2Test` checks that
  `#assert_axioms_T2` rejects theorems that use other axioms.

## Contents

| Directory | Programs | Role | Paper |
|---|---|---|---|
| `ip/` | `seed334.py`, `common334.py` | the seeded table: for each class, its basis, Wang's bound and the seeded bound | Section 5 |
| | `expand334.py`, `mkip334.py`, `mkcand.py`, `s4_labmaps.py` | the IPs of the two point searches; `mkcand.py raise` subtracts 1 from the cap of each raised line and plane | Section 4 |
| | `mkipS9.cc`, `mkipS.py` | the IP of the search for a subspace of dimension 2 or more (C++, and the Python program it was ported from; both write the same file) | Sections 4, 5 |
| `enum/` | `lineenum9vr.cc`, `lineenum9m4.cc`, `lineenum9m8.cc`, `packlp.h` | the search: orderly enumeration of profiles under the caps with LP pruning, writing the proof trace (variants for label caps up to 3, 4 and 8) | Section 4 |
| | `mk_m4.py`, `mk_m8.py` | derive `lineenum9m4.cc` from `lineenum9vr.cc`, and `lineenum9m8.cc` from `lineenum9m4.cc`, by text replacements, each of which must match a set number of times | Section 4 |
| | `lechk9vr.cc`, `lechk9m4.cc`, `lechk9m8.cc` | the replay: re-checks every block of a trace and the coverage of the search tree | Section 4 |
| `run/` | `table_class.sh` | one search of the class table: IP, search, replay, and the leaf questions | Sections 4, 5 |
| | `rounds_search.sh`, `rounds_replay.sh`, `rounds_complete.sh` | a search in rounds (the two point searches and the heaviest planes), its replay, and its leaf questions | Section 4 |
| `leaves/` | `mkcompS9.cc`, `mkcompS.py`, `tsolve334.cc` | the leaf questions of a search (C++ and Python, same output) and their exact solver | Sections 4, 6 |
| | `gen7_334.cc`, `gen7_334.h`, `model334.h`, `symtab334.h` | the branching certificates of the leaves | Section 6 |
| | `s18_bctab.py` | the literal tables of the Lean certificate checker (`B334/BC/Tables334`) | Section 6 |
| | `s20_t2gen.py` | the modules `B334/T2` of the certificate records: each record is checked by `decide +kernel` or, for 811 records, by a single `native_decide` theorem that covers them all | Sections 6, 7 |
| | `s26_leafmatch.py` | matches each search leaf with its certificate record (`leaf_match.tsv`) | Section 7 |
| `check/` | `chk334e.cc`, `chk334c.cc` | the trace checker and the certificate checker, each written from a description of the file formats (`chk334e` also from the input files), without reading the search code | Section 7 |
| `table/` | `s21_tab2.py`, `s23_monowit.py` | the class table `table_v2.tsv` (the argument and bound of each class) and the witnesses of its monotone classes | Section 5 |
| | `s22_tab2lean.py` | the table as Lean data (`B334/Tab2`) | Sections 5, 7 |
| | `emit_k.py`, `s16_flatcert.py`, `s14_gen_krow.py` | the forced-product witnesses and the flattening certificates, and their modules (`B334/MethodK/Rows`) | Section 5 |
| | `s16_row44.py` | the coset-counting certificate of class 44 (`B334/Bind/Row44Certs`, `Row44C<k>`) | Section 5 |
| | `s13_gen_symtab.py`, `s13b_gen_symtab_split.py` | the pair-symmetry tables of the first branching (`B334/Tables`, `symtab334.tsv`) | Section 6 |
| | `gen_wit.py` | the orbit witnesses of the points (`B334/Lem/OrbitTab`) | Sections 2, 3 |
| `convert/` | `conv_e1g.py`, `conv_e1g_v1.py`, `gen_ipok.py`, `gen_ipok692.py`, `versions/` | traces of the table searches to data files and modules (`B334/E1x/R<c>`, `I<c>`, `Rep<c>`, and the class modules `Cls*`) | Section 7 |
| | `conv_e1p.py`, `versions/S707/conv_e1p.py`, `gen_ipok_p.py`, `repack.py`, `join6.py`, `joinfin.py`, `relocate707.sh` | the same for the two point searches (`B334/E1x/Pts/S707`, `S708`, `H707`, `H708`) | Section 7 |
| | `mk_batch.sh`, `mk_lf_halves.sh`, `mk_lfb_kls.awk`, `mk_fin_join.sh`, `mk_fin_join.awk` | module tools used after the conversion: the batch modules, and the split of the largest table search, `R619` | Section 7 |
| `inputs/` | `seeded334.tsv`, `table_v2.tsv`, `mono_wit.tsv`, `certs334.tsv`, `e707_times.txt` | input tables of the runs (described at the end) | |

`build.sh` compiles the C++ programs; `LICENSE` is the Apache License 2.0.

## Requirements and build

- **C++.** A C++17 compiler. `bash build.sh OUTDIR HIGHS_LIBDIR [MARCH]` builds the twelve programs into `OUTDIR`
  with the optimization flags of the original builds: `-O3` for the three search and three replay programs, `-O2` for
  the others. For the original runs, nine programs (the search and replay programs, `mkipS9`, `mkcompS9` and
  `tsolve334`) were also built with `-march=znver4` and a static C++ runtime; the original build scripts of
  `gen7_334`, `chk334c` and `chk334e` add neither by default. `build.sh` passes `-march=MARCH` (default `native`; the
  rerun used `znver4` and g++ 15.2) to the nine, links the C++ runtime statically into all twelve, and builds
  `chk334c` without zlib (see "Changes from the programs that ran"). The search programs call the HiGHS C API (MIT
  license): run `pip install highspy==1.15.1` and pass the package directory (`site-packages/highspy`, which holds
  `libhighs.so.1`) as `HIGHS_LIBDIR`. `build.sh` copies the library into `OUTDIR`, so `OUTDIR` is self-contained.
- **Python.** The converters and the table, certificate and module generators need only the Python 3 standard
  library; they ran under Python 3.12 or 3.13. The programs in `ip/` and `leaves/mkcompS.py` need numpy, scipy (for
  the LP at the end of `seed334.py`) and numba (for `expand334.py` and `mkipS.py`). They ran under Python 3.12 with
  numpy 2.5.3, scipy 1.18.1 and numba 0.68.0, in both the original runs and the rerun; the rerun used Python 3.13 for
  the other scripts. Run the scripts with `python3 -I` (isolated mode, which ignores `PYTHON*` variables and user site
  packages and keeps the script's directory off the module path); `-B`, used in step 5, only stops Python from writing
  `.pyc` files.
- **Shell.** bash, coreutils and awk; `mk_fin_join.sh` needs GNU awk.
- **External inputs.** `seed334.py` reads two certificate files from Wang's repository
  (https://github.com/wcgbg/tensor-rank-lower-bound, commit d96d787b, MIT license):
  `certs/matrix/cert_matrix_q02_n333.pb.txt` (sha256 `25595a88…`) and `certs/matrix/cert_matrix_q02_n334.pb.txt`
  (sha256 `14f1b9fc…`), and two files from the `rank333-f2` record (doi:10.5281/zenodo.23236154):
  `lean/HC/RRTable.lean` and `data/classes/routes.tsv`. `mkcompS9` and `mkcompS.py` take a decomposition of ⟨3,3,4⟩
  of rank 29 as input (`SCHEME` below), one product `(a-form)*(b-form)*(c-form)` per line. The original runs used
  copies of `solutions/334-29-mod0.exp` from the flip-graph repository of M. Kauers and J. Moosbauer
  (arXiv:2212.01175); the rerun used that file and reproduced the original positive controls byte for byte. The
  decomposition only feeds the positive control `pos_c<c>.a`; no file of this archive depends on it. The converters
  read three release modules: `lean/B334/E1x/TabG.lean`, `TabP.lean` and `ClsTab.lean`.

The IP files of the two point searches (30 MB each) and the proof traces of the searches are not included. Step 1
below regenerates the IP files byte for byte. Rerunning a search regenerates its trace: a one-thread search
(`table_class.sh`) writes the same trace, but a search in rounds on many threads writes some blocks differently, and
then the data files converted from it differ too (see "What was rerun for this archive").

## The original runs

The commands below use these placeholders; bare file names are relative to the working directory of the run.

| Name | Meaning |
|---|---|
| `S` | this directory |
| `BIN` | `build.sh`'s output directory |
| `TABLE` | `inputs/seeded334.tsv` |
| `SCHEME` | the rank-29 decomposition named above |
| `WANG`, `RANK333` | a copy of Wang's repository; the unpacked `rank333-f2` record |
| `C`, `L` | a class number and a search length |
| `IN`, `OUT` | the input and the output of a program, a file or a directory (its docstring or header says which) |
| `TRACES`, `THREADS` | a point search's trace directory; a number of threads |
| `LEANDIR` | the `lean/` directory of the tree that a module tool changes |
| `RECORD` | the unpacked archive |

### 1. The seeded table and the IPs

`RL` and `PL` list the raised lines and planes:

```
RL=702,696,693,694,691,697,695,705,692,690
PL=610,613,615,618,619,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,677,678,679,680,681,682,683,684,685,686,687
PL8=$PL,632,636        # the command for E = span(v3) listed 632 and 636 too; its IP has no cap for them
python3 -I S/ip/seed334.py WANG/certs/matrix RANK333 data       # data/seeded334.tsv (= TABLE) and data/seeded334.npz
python3 -I S/ip/expand334.py --data data                         # data/sup_P706.npz, sup_P707.npz, sup_P708.npz (19 s)
python3 -I S/ip/mkip334.py 707 seeded 25 ip_P707_seeded_L25.txt --data data
python3 -I S/ip/mkcand.py raise ip_P707_seeded_L25.txt 707 $RL,$PL ip_P707R2b_seeded_L25.txt --data data
python3 -I S/ip/mkip334.py 708 seeded 25 ip_P708_seeded_L25.txt --data data
python3 -I S/ip/mkcand.py raise ip_P708_seeded_L25.txt 708 $RL,$PL8 ip_P708R2_seeded_L25.txt --data data
python3 -I S/ip/s4_labmaps.py data --data data                   # data/lab2cos_P706.txt, _P707.txt, _P708.txt
```

The IP of a table search comes from `BIN/mkipS9 TABLE C L OUT --maxgroup 2048` (the first step of
`run/table_class.sh`); the IPs of the raised lines and planes were written by
`python3 -I S/ip/mkipS.py C L OUT --data data`, and `mkipS9` writes the same files.

### 2. The searches

The two point searches (E = span(v2), run name `707R2b`; E = span(v3), run name `708R2`) ran in rounds on a machine
with 180 virtual cores, in the directory of their IP file:

```
bash S/run/rounds_search.sh BIN 707R2b 176 30000
bash S/run/rounds_replay.sh BIN 707R2b 64              # must print RESULT PASS and coverage COMPLETE
bash S/run/rounds_complete.sh BIN 707R2b q10.t data/lab2cos_P707.txt
```

and the same for `708R2` with the target `q84.t`. The targets `q10.t` and `q84.t` (T mod E in reduced coordinates)
are byte-identical to the files `qS_c707.t` and `qS_c708.t` that `mkcompS9` writes for these two classes (it needs
no leaf files for that: a missing leaf file counts as empty). Running times and leaf counts:

| Run | Search | Replay | Leaves |
|---|---|---|---|
| `707R2b` | 31 minutes (first pass and 2 rounds) | 12 seconds | 1 |
| `708R2` | 33 minutes (first pass and 3 rounds) | 52 seconds | 0 |

Each table search covers one class (the backtracking rows ran 40 at a time):

```
bash S/run/table_class.sh BIN TABLE SCHEME C L
```

The 301 backtracking rows of Wang's table were searched with L = seeded bound − 1, to confirm that bound; the run took
11 seconds of wall time. 293 were confirmed by a search, 7 needed no search (a strict superspace already has a bound
above L), and class 44 got its bound from coset counting instead (its label caps exceed 8). The lifted rows and the
raised lines and planes used the lengths in the columns `lift_L` and `raised_L` of `inputs/table_v2.tsv`. The option
`--sibk 4`, which `table_class.sh` passes by default, keeps the last 4 LP certificates at each depth and tries them
before solving a new LP. The searches of the backtracking and lifted rows used it; those of the raised lines and
planes did not (an empty `SIBK` in the environment turns it off). The heaviest planes, classes 618, 619, 660, 667,
672, 673, 677 to 683, 686 and 687, ran in rounds like the point searches: `rounds_search.sh BIN pl<c> THREADS 30000`
with `IPF=ipS_c<c>_L23.txt LPMAX=22` (L − 1) in the environment (and `ENUM=lineenum9m4`, `CHK=lechk9m4` for class
618, whose label caps reach 4).

`table_class.sh` writes the leaf questions with `BIN/mkcompS9 TABLE SCHEME COMPDIR LEAFDIR C` (from the leaf files in
`LEAFDIR` into `COMPDIR`) and runs `tsolve334` on them with a time limit of 60 seconds, then 600 seconds for the
leaves left undecided. `rounds_complete.sh` writes the instances `inst_P<C>_0.a` from the leaves and the label map,
takes the target as an argument, and uses time limits of 60, 600 and 3600 seconds in turn.

### 3. Certificates

The certificates come from `gen7_334`, run on the leaf questions that `mkcompS9` writes (the target `qS_c<C>.t` and the
instances `inst_c<C>.a`):

```
BIN/gen7_334 --target qS_c<C>.t --Ks 4,8 --maxnodes 300000 --deadk 6 --hex OUT.hex inst_c<C>.a \
    --symtab symtab334.tsv --seeded TABLE
```

The original runs left `--symtab` and `--seeded` at their defaults, the files `symtab334.tsv` and `seeded334.tsv` in
the directory `../data/` relative to the program.

For the leaf of the point search the options were `--target q10.t --class 707 --Ks 4,8 --maxnodes 300000 --deadk 6
--mutants 20`, on the instance file `inst_P707R2b_0.a` that `rounds_complete.sh` writes. Each line of `OUT.hex` is
`tag nbits hex`, the certificate of one leaf; `BIN/chk334c --E <basis of the class> --hex FILE` checks a file
that holds the hex field of one such line. `s20_t2gen.py` turns the certificate records into the modules `B334/T2`:

```
python3 -I S/leaves/s20_t2gen.py OUT --units UNITS --stats STATS --p707 leaf.hex --p707-stats p707_stats.txt --lift LIFT
```

`UNITS/C/jobs.txt` lists the certificate files of the plane leaves, and `LIFT` holds the certificates and statistics
of the 19 leaves of the lifted rows. `STATS` and `p707_stats.txt` give, for each record, the line `c tag nbits`
followed by the `nodes=…` part of the output of `chk334c_stats`, a variant of `chk334c` that adds work counts to each
`ACCEPT` line. Its source is `evidence/kernel_cost/chk334c_stats.cc` in the archive, a single C++17 file without
external libraries; compile it as `build.sh` compiles `chk334c`. `leaf_match.tsv` (search leaf to certificate record)
comes from `python3 -I S/leaves/s26_leafmatch.py IN OUT`, whose docstring lists the files of `IN`.

### 4. The class table and its modules

```
python3 -I S/table/s21_tab2.py IN OUT          # OUT/table_v2.tsv and table_v2_summary.txt; IN: see the docstring
python3 -I S/table/s23_monowit.py IN OUT       # OUT/mono_wit.tsv
python3 -I S/table/s22_tab2lean.py inputs/table_v2.tsv lean/B334/Tab2 inputs/mono_wit.tsv
python3 -I S/table/emit_k.py emit KDIR 6 12 13 16 17 23 26 28 33 35 37 38 41 42 45 52 54 55 65 135 147 \
    --seeded TABLE --certs inputs/certs334.tsv
python3 -I S/table/s16_flatcert.py FDIR --table TABLE
python3 -I S/table/s14_gen_krow.py KDIR/row<c>.json lean/B334/MethodK/Rows CHUNK  # per row; FDIR/row<c>.json if f = 0
python3 -I S/table/s16_row44.py row44.json --table TABLE
python3 -I S/table/s16_row44.py row44.json certs
python3 -I S/table/s16_row44.py row44.json lean lean/B334/Bind
python3 -I S/table/s13_gen_symtab.py lean/B334/Tables/SymTab.lean symtab334.tsv
python3 -I S/table/s13b_gen_symtab_split.py lean/B334/Tables/SymTab.lean SPLIT/B334/Tables
python3 -I S/leaves/s18_bctab.py lean/B334/BC/Tables334.lean symtab334.tsv
python3 -I S/table/gen_wit.py lean/B334/E1x/GLTab.lean lean/B334/Lem/OrbitTab.lean
```

Output directories: `s21_tab2.py`, `s23_monowit.py` and `s16_flatcert.py` refuse an existing one; `s14_gen_krow.py`
creates its own if needed; `s13b_gen_symtab_split.py` stops if `SPLIT/B334/Tables/Split` exists (`SPLIT` is any new
directory); the others need it to exist. `emit_k.py`
writes the 21 forced-product rows (a row file and a negative-control file for each), and `s16_flatcert.py` the 18 rows
whose bound is a flattening rank, in the same format with f = 0 (no forced products; f as in Section 5). `CHUNK` is
64 for rows 16, 55, 65, 135 and 147 and 512 (the default) for the others. `s13_gen_symtab.py` also writes `SymTabOrb`
and `SymTabWC_<o>`; the released ones are those that `s13b_gen_symtab_split.py` writes, which check the same facts in
smaller parts.

### 5. Data files and modules of the searches

The data files of a table search lie in `runs/<tag>/`, where `<tag>` names the conversion run. A run used the commands
below in a directory named `<tag>` (`conv_e1g_v1.py run` takes the data path `../runs/<tag>` from that name). `IP`,
`TRACE` and `BASIS` are the IP file, the trace file and the basis of the class (the column `basis` of `TABLE`),
`TabG.lean` is the module `lean/B334/E1x/TabG.lean`, and `leaf_match.tsv` comes from step 3:

| Run tags | Data files | Modules |
|---|---|---|
| `gensim3`, `gensimp2` | `conv_e1g.py IP TRACE --basis BASIS --tabg TabG.lean --bin blk_R<c>.bin` | `gen_ipok.py IP table_v2.tsv --cls <c> --ns R<c> --src <file name of IP> --bin --binrel ../runs/<tag> --blkbin blk_R<c>.bin --single` |
| `genlines1` | as `gensim3` | as `gensim3`, without `--single` |
| `genleaf1`, `genleaf2`, `genleaf3`, `genleaf5` | `conv_e1g_v1.py single IP TRACE --tabg TabG.lean --out c<c>` | `gen_ipok.py IP table_v2.tsv --cls <c> --ns R<c> --src <file name of IP> --bin --binrel ../runs/<tag> --blkbin c<c>_blk.bin --blkinfo c<c>_info.txt --leafmatch leaf_match.tsv` |
| `gen696a` | as `genleaf1` | as `genleaf1`, without `--leafmatch` |
| `gen4a`, `gen693b` | (the block literal is in the module `Rep<c>`) | `gen_ipok.py ipS_c<c>_L23.txt table_v2.tsv --cls <c> --ns I<c> --src ipS_c<c>_L23.txt --blk Rep<c>.S --bin --binrel ../runs/<tag>` (for `gen693b`: `--ns I693t --blk Rep693d.S`) |
| `run672c`, `runmulti2` | `conv_e1g_v1.py run IP --traces LIST --tabg TabG.lean --ns R<c> --cls <c> --ebasis BASIS --leafmatch leaf_match.tsv --jobs 48` (`LIST`: the trace files of the class, one per line; `--jobs 32` for `run672c`) | `gen_ipok.py IP table_v2.tsv --cls <c> --ns R<c> --src <file name of IP> --bin --binrel ../runs/<tag> --leafmatch leaf_match.tsv` |

`gen_ipok.py` writes the slot tables `tab_<ns>.bin` and `sl_<ns>.bin` and prints the modules, each between a line
`=== FILE <path under lean/>` and a line `=== END`; `conv_e1g_v1.py run` prints its modules the same way. This awk
command writes them into a directory `out/`:

```
awk -v L=out '/^=== FILE /{f=L"/"$3; d=f; sub(/\/[^\/]*$/,"",d); system("mkdir -p \"" d "\""); next}
  /^=== END/{close(f); f=""; next} f!=""{print > f}' gen.out
```

`convert/gen_ipok.py` is the latest version of the module generator. The tags `gensim3`, `gensimp2`, `genlines1`,
`genleaf5`, `run672c` and `runmulti2` ran four versions of it (one for `gensim3` and `gensimp2`, one for `genlines1`,
one for `genleaf5`, and the latest for `run672c` and `runmulti2`), and the latest writes the same modules for all six
(checked on classes 402, 694, 658, 618 and 619; for 618 and 619 apart from the modules changed after the conversion,
listed below). For the other tags it writes a different module layout or different table entries, so they need the
earlier versions kept in `convert/versions/`:

| Run tags | Regenerate the modules with |
|---|---|
| `genleaf1`, `genleaf2`, `genleaf3` | `convert/versions/genleaf1/gen_ipok.py` |
| `gen696a` | `convert/versions/gen696a/gen_ipok.py` |
| `gen4a`, `gen693b` | `convert/versions/gen4a/gen_ipok.py` |

`genlines1` ran the same version as `genleaf1` to `genleaf3`, but it has no block-info file, and for it the latest
version writes the same modules (checked on class 694). `conv_e1g_v1.py` writes the same data files as the earlier
versions that `genleaf1`, `genleaf2`, `genleaf3`, `genleaf5` and `gen696a` ran (checked on classes 27, 301, 657, 658
and 696). The option `--jobs` of the converters sets the number of worker processes; the workers' results are
collected in order, so the output does not depend on it (checked for `conv_e1p.py`: 170 workers instead of 48 give
the same S708 files).

Modules without data files of their own:

- `I692` and the class modules `ClsTab`, `ClsBase`, `ClsOK0` … `ClsOK7`, `ClsAll`: `gen_ipok692.py ipS_c692_L22.txt
  table_v2.tsv --cls 692 --ns I692 --src ipS_c692_L22.txt --glob --blk Rep692b.S`.
- The block modules `Rep691`, `Rep692b`, `Rep693d`, `Rep697`, `Rep702` and `Rep705`: `conv_e1g.py IP TRACE --basis
  BASIS --tabg TabG.lean --lean Rep<c>.lean --ns B334.E1x.Rep<c>`. They were written by an earlier version of
  `conv_e1g.py`, which is lost. The version here writes the same literals (checked for `Rep691`: the block, its three
  mutants, the label bounds, the labels, the domain and the identity permutation) but stores the slot table in a
  different form, so the module text differs.
- The batch modules `RB/Batch1` … `RB/Batch8`, `RB/BatchLeaf1` and `RB/BatchMulti`: `mk_batch.sh OUT NAME "IMPORTS"
  "CLASSES"`.
- The modules of the largest table search, `R619`, were changed in four steps after the conversion:
  1. its leaf check was rewritten to read the certificate records through the lists of the T2 modules:
     `awk -v NS=R619 -v C=619 -v GEN="generated by a script" -f mk_lfb_kls.awk LISTS > LfB.lean`, where `LISTS` has
     the lines `name start length` of the lists `kl_619_<k>` and `nl_619` in the order of `T2.leaves_619`;
  2. to use the new `LfB`, the proof `hLF` in its `Fin` was edited by hand: `have hm := getD_mem hc.1` replaces the
     three-line membership proof of `hm`, and `(klsGetOK _ _ hm)` replaces `(T2.ok_619 _ hm)`;
  3. its leaf checks were split into halves: `mk_lf_halves.sh LEANDIR R619 5440 50`;
  4. its `Fin` was split into joined parts: `mk_fin_join.sh LEANDIR R619 OLDFIN WORKDIR 1500 100`, with the edited
     `Fin` of step 2 as `OLDFIN`.
- The axiom gates `Ax` of `R618`, `R619`, `R667` and `R682` were replaced by hand with gates that also allow the axiom
  of the `native_decide` check in `B334/T2/N_0`, because records checked there cover some leaves of these runs.

The two point searches:

```
# S707, in a directory stage707_v3:
python3 -I -B S/convert/versions/S707/conv_e1p.py run ip_P707R2b_seeded_L25.txt --traces 'TRACES/P707R2b_*' \
    --tabp TabP.lean --ns S707 --ipns H707 --cls 707 --R 25 --ebasis 10 \
    --leaves fcf9e6dfd7c5b6b1a49f8f83493f221f1d1309050302020101 --t2i 0 --jobs 48 --ipS 102
# in stage707_v5:
python3 -I -B S/convert/repack.py ../stage707_v3 S/inputs/e707_times.txt
# in stage707_v6, with stage707_v5's Fin.lean and Ax.lean copied to fin_v5.lean and ax_v5.lean:
python3 -I -B S/convert/join6.py 1500
# MODS: the S707 modules of stage707_v3, overwritten by those of stage707_v5, then by those of stage707_v6;
# DATA708: the data directory of S708
bash S/convert/relocate707.sh stage707_v3/data DATA708 MODS OUT

# S708, in a directory stage708b_v1 (--dump only saves the results as a pickle, res.pkl):
python3 -I -B S/convert/conv_e1p.py run ip_P708R2_seeded_L25.txt --traces 'TRACES/P708R2_*' \
    --tabp TabP.lean --ns S708 --ipns H708 --cls 708 --R 25 --ebasis 84 --jobs 48 --ipS 102 --dump res.pkl
python3 -I -B S/convert/joinfin.py S708 H708 lean/B334/E1x/Pts/S708/Fin.lean lean/B334/E1x/Pts/S708/Ax.lean jout 1500
# the modules in jout/B334/E1x/Pts/S708/ go next to the other S708 modules, and its Fin.new replaces Fin.lean

# H707 (and H708 likewise), in a directory genp_h707a:
python3 -I S/convert/gen_ipok_p.py ip_P707R2b_seeded_L25.txt table_v2.tsv --cls 707 --ns Pts.H707 \
    --src ip_P707R2b_seeded_L25.txt --bin --binrel ../runs/genp_h707a --clstab ClsTab.lean --negctl 1000
```

The modules of `H707` were unpacked with `../runs/genp_h707a/` replaced by `../data/`, and its tables
`tab_Pts_H707.bin` and `sl_Pts_H707.bin` were copied to `data/` (likewise for `H708`); `--binrel ../data` writes the
released modules directly. `--leaves` is the packed prefix of the span(v2) search's only leaf, and `--t2i 0` the
index of its record in `T2.leaves_707`. Both versions of `conv_e1p.py` write the same S707 data files, but only the
earlier one writes the released S707 modules: the later one packs the modules of the large jobs by predicted memory.
`repack.py` re-packs the jobs whose modules needed too much memory in a first build, as recorded in
`inputs/e707_times.txt`. `relocate707.sh` repeats a step that was done by hand: the S707 data files whose names clash
with S708 data files were moved to `data707/`, and the S707 modules that read them were changed to read
`../data707/<f>`. The S707 conversion took 456 seconds with 48 worker processes (16,329 seconds of worker time), the
S708 conversion 62 minutes (170,618 seconds of worker time).

## Checking the outputs

`DATA_SHA256SUMS` (and `DATA_SHA256SUMS_TESTS` for the test target) lists the released data files with paths
relative to `lean/`: `../data/<f>`, `../data707/<f>` and `../runs/<tag>/<f>`. The modules are listed in
`evidence/checks/3a_release_snapshot_on_box.sha256` (the sha256 list of the release tree, taken on the reference Lean
build machine), with paths `lean/B334/…`. To check a regenerated file, look up the same path; for the data
files of a run regenerated in a directory `gensim3`:

```
cd gensim3
for f in *.bin; do
  want=$(awk -v p="../runs/gensim3/$f" '$2 == p {print $1}' RECORD/DATA_SHA256SUMS)
  [ "$(sha256sum < "$f" | cut -c1-64)" = "$want" ] && echo "$f equal" || echo "$f differs"
done
```

For modules unpacked under `out/` (`out/B334/…`), look up `lean/B334/…` in
`RECORD/evidence/checks/3a_release_snapshot_on_box.sha256` the same way.

## What was rerun for this archive

The C++ programs were built with `build.sh` (g++ 15.2, `MARCH` = `znver4`) from a clean copy of this directory on one
machine, and the programs were rerun on the original inputs on another, with 180 virtual cores. Two checks ran on the
machine that built the programs: `mk_fin_join.sh` and the point targets of `mkcompS9`. The edits made after these runs
are listed at the end of the next section.

The table searches on one thread (`table_class.sh`) wrote the same IPs and traces byte for byte. The two reruns on
many threads did not: the raised plane 672, run in rounds, wrote 2,562 of its 2,714 blocks byte for byte as the
original run did, and chunk 0 of round 2 of the span(v2) search wrote 2,976 of its 3,146 blocks so. In both, the
blocks cover the same subtrees (they have the same prefixes), the totals agree with the original runs (plane 672:
2,709 jobs, 355,703 nodes and 175 leaves; the chunk: 3,138 jobs, 3.927 × 10⁵ nodes as its log prints them, and no
leaves), and the replays pass with coverage complete. We did not trace every differing block, but the first
difference in each rerun is of one kind: a record names a different row. On many threads, which thread takes which
job depends on timing, and each thread keeps its search state from one job to the next, including, at each depth, up
to four rows it found binding, which it tries first when it bounds the next label. Where several rows give the same
bound or rule out the same label, a record can then name a different one: the first difference in plane 672 is the
row named by an `O` record (2130 in one run, 2062 in the other, with the same cut), in the chunk the row named by a
`P` record (416697 and 406334). The subtrees and leaves stay the same, and the replays check every block, so the
blocks stay valid. The other comparisons in the table are byte-identical except where a row or a note says otherwise.

| Step | Programs | Compared with the original files | Result |
|---|---|---|---|
| IPs | `seed334.py`, `expand334.py`, `mkip334.py`, `mkcand.py`, `s4_labmaps.py`, `mkipS.py`, `mkipS9` | `seeded334.tsv`; the IPs of both point searches; the label maps of 707 and 708; the IP of class 702 (L 23); the IPs of classes 402, 27, 301, 100, 431, 694 and 658 | all byte-identical |
| Table searches | `table_class.sh` with the programs of `enum/` and `leaves/` | classes 27 (`lineenum9vr`), 402 and 301 (`lineenum9m4`), 100 and 431 (`lineenum9m8`), and with `SIBK=` the raised line 694 and the raised plane 658: IPs and traces; for 27 and 301 also the leaves | all byte-identical; the replays pass with coverage complete; `tsolve334` refutes all 182 leaves (1 for 27, 6 for 301 and 175 for 658) |
| | `mkcompS9`, run by `table_class.sh` | the leaf questions of 27 and 301 (`qS_c<c>.t`, `inst_c<c>.a`, `pos_c<c>.a`) | byte-identical |
| | `mkcompS.py` | the same six files | byte-identical to those of `mkcompS9` |
| | `mkcompS9` | the targets `q10.t` and `q84.t` of the point searches | byte-identical |
| | `chk334e` | the traces of 402, 27 and 301 | RESULT PASS |
| Search in rounds | `rounds_search.sh`, `rounds_replay.sh` | the raised plane 672 (10 seconds) | the same 2,709 jobs, 355,703 nodes and 175 leaves; the replay passes with coverage complete; 2,562 of the 2,714 blocks are byte-identical |
| Point search | `lineenum9vr`, `lechk9vr` | round 2, chunk 0 of the span(v2) search (8 roots, 176 threads, 82 seconds) | the same 3,146 blocks (by their prefixes), of which 2,976 are byte-identical (note 1) |
| Point conversions | the S707 and S708 steps of step 5, `gen_ipok_p.py` | all modules of `B334/E1x/Pts/S707` (2,751), `S708` (28,373), `H707` and `H708` (106 each), and their data files (989 for S707: 941 in `data/`, 47 in `data707/` and one of the test target; 11,829 for S708, one of them of the test target; 2 each for H707 and H708) | all byte-identical (note 2) |
| Table conversions | `conv_e1g.py`, `conv_e1g_v1.py`, `gen_ipok.py` and its versions | classes 402 (`gensim3`), 27 and 301 (`genleaf1`), 657 (`genleaf3`), 658 (`genleaf5`), 694 (`genlines1`), 696 (`gen696a`), 691, 697, 702 and 705 (`gen4a`), 618 and 619 (`runmulti2`): all their modules and data files (109 data files for 618 and 803 for 619, each including one file of the test target) | all byte-identical, except the modules changed after the conversion (step 5; note 3) |
| | `gen_ipok692.py`; `mk_batch.sh` | the 13 modules of `I692` and the 11 class modules; the 10 batch modules | byte-identical |
| | `mk_lfb_kls.awk`, `mk_lf_halves.sh`, `mk_fin_join.sh` | `LfB` of R619; its 164 leaf modules; its 17 joined modules | byte-identical (note 4) |
| | `conv_e1g.py --lean` | `Rep691` | the same literals, a different layout (see step 5) |
| Class table and modules | `s21_tab2.py`, `s23_monowit.py`, `s26_leafmatch.py`, `s13_gen_symtab.py`, `s16_row44.py`, `s20_t2gen.py` | `table_v2.tsv`, `mono_wit.tsv`, `leaf_match.tsv`, `symtab334.tsv`, `row44.json`, the T2 manifest | byte-identical |
| | the generators of step 4 and `s20_t2gen.py` | the modules `Tab2/Data` and `Tab2/DegData`; 146 of the 148 modules of `B334/Tables` (all but the hand-written `SymFacts` and `Split/Range`); `B334/BC/Tables334`; `B334/Lem/OrbitTab`; `B334/Bind/Row44Certs` and `Row44C0` … `Row44C7` (9); `B334/MethodK/Rows` (709); `B334/T2` (219) | byte-identical |
| | `emit_k.py`, `s16_flatcert.py` | the 42 and 18 JSON files of the forced-product and flattening rows | byte-identical except `row54.json` (note 5) |
| | `mk_m4.py`, `mk_m8.py` | `lineenum9m4.cc`, `lineenum9m8.cc` | derived exactly |
| Certificates | `gen7_334`, `chk334c` | the certificate records of the leaves of classes 27 and 301 and of the point search (9 records: the point leaf has two) | byte-identical, matching the sha256 prefixes in the T2 manifest; `chk334c` accepts all 9 |

Notes:

1. With the 170 rerun blocks that differ in place of the original ones, the replay of the whole search passes with
   coverage complete, and the conversion gives 810 of the 941 data files in `data/` unchanged and 131 changed.
2. The S707 steps also write the 1,002 modules `K<k>C<j>` of the jobs that `repack.py` re-packs, and the S707 and S708
   conversions each write the five negative-control modules of their run, which belong to the test target. Neither
   set is in the module list of the release, and neither was compared. The S708 conversion took 33 minutes with 170
   worker processes.
3. The modules changed later are `Ax` of 618 and 619, and `LfB`, the `Lf<k>` and `Fin` of 619. The block-info files
   of 27 and 301, which are not data files, differ from the original ones only in the trace file name on their first
   line. The tags `gensimp2`, `genleaf2`, `gen693b` and `run672c` ran the same program versions as `gensim3`,
   `genleaf1`, `gen4a` and `runmulti2`, so they were not rerun separately.
4. `OLDFIN` was the `Fin` that `conv_e1g_v1.py` writes, with the hand edit of step 5. The edited `Fin` kept from the
   original run starts with the docstring line of the older converter; with that file as `OLDFIN`, the joined `Fin`
   differs from the released one only in that line.
5. `row54.json` differs in the wording of its field `choice`: the new wording, "a hand-picked subset", is the one in
   `R54D`.

## Changes from the programs that ran

These are the programs that produced the archive, changed only as follows:

- Comments and docstrings were reworded to remove working notes, internal labels and dates, including the comment
  lines that `mk_m4.py` and `mk_m8.py` insert into the sources they derive (and the line `mk_m8.py` matches). So were
  some printed messages and usage texts (of `gen7_334`, `chk334c`, `chk334e`, `emit_k.py`, `s22_tab2lean.py`,
  `gen_ipok.py` and the drivers) and the notes that `repack.py` and `join6.py` write next to their outputs.
- Absolute paths became arguments or relative paths:
  - `--data DIR` of the programs in `ip/` and of `mkcompS.py`, the inputs of `seed334.py`, the output directory of
    `s4_labmaps.py`, and `--scheme` of `mkcompS.py`; the programs that import `common334.py` find it in `ip/`;
  - the inputs of `s20_t2gen.py`, `--table` of `s16_flatcert.py` and `s16_row44.py`, the second argument of
    `s18_bctab.py`, and `--seeded` and `--certs` of `emit_k.py`;
  - the Lean directory of `mk_lf_halves.sh` and `mk_fin_join.sh`, and the work directory of `mk_fin_join.sh`, which
    now finds `mk_fin_join.awk` next to itself;
  - the program directory, an argument of each driver in `run/`;
  - the last fallback of `gen7_334` for its data files, now `data/<name>`.
  The path constants of `common334.py`, which only `seed334.py` used, and an unused one in `s26_leafmatch.py` were
  removed. `repack.py` takes its two inputs as optional arguments, whose defaults are the relative paths it used.
- The drivers in `run/` were adapted from the original ones and renamed: `routeb1.sh` became `table_class.sh`,
  `run_class3.sh` (`run_class2.sh` with the enumerator taken from `ENUM`) became `rounds_search.sh`, `replay.sh`
  became `rounds_replay.sh` and `complete.sh` became `rounds_complete.sh`. `table_class.sh` runs one class with a
  given L. `routeb1.sh` ran the 301 backtracking rows
  from a list, 40 at a time, with L = seeded bound − 1; it kept a status log, stopped on the marker files `STOP` and
  `STOP_SAT`, skipped rows already done, and always passed `--sibk 4` (the variable `SIBK` is new). The original
  round drivers did not start the search for class 707 until a marker file existed; that check is gone.
  `rounds_replay.sh` takes the replay program and the IP file from `CHK` and `IPF` (the original used `lechk9vr` and
  `ip_P<C>_seeded_L25.txt`), and `rounds_complete.sh` takes the target and the label map as arguments (the original took
  the target from a built-in table for the classes 706 to 708 and read the label map from `lab2cos_P<C>.txt`). The
  drivers work in the current directory; the originals changed to their own directory (`routeb1.sh` to a fixed run
  directory, where it also wrote a pid file, set `LD_LIBRARY_PATH` and called `mkipS9` by its build name `mkipS9c`).
- The generators print the docstrings of the released modules, which were reworded for the release in the same way:
  `emit_k.py` writes the wording of `R54D` noted above. `conv_e1g.py --lean` now requires the IP file name
  `ipS_c<c>_L<L>.txt`, from which it takes the class number for its docstring, and the top trace (a file `*_top.bin`).
- Code edits that leave every data file and module unchanged:
  - the self-test option of `gen7_334` was renamed (it is `--selftest`), together with its function;
  - an internal function of `chk334e`, a variable of `expand334.py`, some identifiers of `emit_k.py` and one of
    `s21_tab2.py` (now `FLAT17`) were renamed;
  - two checks are gone: `gen_ipok_p.py` no longer requires the table's sha256 in the docstring of `ClsTab.lean` (the
    check that its table equals the computed one stays), and `mk_fin_join.sh` no longer requires its output directory
    to lie under a fixed directory;
  - `mk_fin_join.sh` calls GNU awk, since `mk_fin_join.awk` uses its three-argument `match()`.
- One line of the summary file `table_v2_summary.txt` that `s21_tab2.py` writes was reworded.
- `build.sh` builds `chk334c` without the optional zlib support of its original build script, which only lets it
  read `.gz` input (compile with `-DUSE_ZLIB -lz` to get it).
- New: `build.sh` and `relocate707.sh`, which repeats the step done by hand.

Edits made after the reruns above: comments in `build.sh` and `mk_fin_join.awk`; docstrings in `conv_e1g.py`,
`conv_e1g_v1.py`, both versions of `conv_e1p.py` and `repack.py`; in `s21_tab2.py` the docstring, the renamed
identifier and the reworded summary line; and in `mk_fin_join.sh` a comment and the gawk call, after which it was
tested again (the 17 modules above).

## Third-party code and data

- Some programs are adapted from programs in `rank333-f2`, the record of the proof that R_F₂(⟨3,3,3⟩) = 23
  (doi:10.5281/zenodo.23236154, Apache-2.0): `enum/packlp.h` is its `cpp/include/packlp.h`, unchanged;
  `enum/lineenum9vr.cc` (and so `lineenum9m4.cc` and `lineenum9m8.cc`) derives from a version of its search
  `cpp/enum/lineenum9qe.cc`; `leaves/tsolve334.cc` from `cpp/tsolve/tsolve4.cc`; `leaves/gen7_334.cc` and
  `gen7_334.h` port `cpp/enum/gen7c.cc` and `gen7.h`; the E1 model in `conv_e1g.py`, `conv_e1g_v1.py` and
  `conv_e1p.py` ports `Job::check` and `node2` of `cpp/enum/e1pemit.h`; and `leaves/symtab334.h` follows the encoding
  conventions of the `rank333-f2` generator. The headers of the adapted files say what changed.
- No code comes from Wang's repository. The tables in `inputs/` contain data derived from Wang's certificate
  files (MIT license); the license notice is in `inputs/WANG-LICENSE.txt`.
- HiGHS, numpy, scipy and numba are installed separately.
- The data in `inputs/` are licensed under CC-BY-4.0, like the other data of this archive, with Wang's notice for the
  parts that come from the certificate files.

## Inputs

- `seeded334.tsv`: one line per class (710): index, dimension, basis (9-bit masks), the numbers of points of rank 1,
  2 and 3, Wang's bound and argument, the ⟨3,3,3⟩ class and its bound, the gain, the seeded bound and the largest
  flattening rank. Written by `seed334.py`.
- `table_v2.tsv`: the class table: the bounds the point IPs use, the argument that proves each bound (column `route`)
  and its evidence. Written by `s21_tab2.py`; its columns are listed in the script's docstring.
- `mono_wit.tsv`: the witnesses of the classes whose bound comes from a superspace (monotone rows). Written by
  `s23_monowit.py`.
- `certs334.tsv`: the 710 entries of `cert_matrix_q02_n334.pb.txt` of Wang's repository as a table (index, rows,
  bound, argument, parameters), read by `emit_k.py` and `s21_tab2.py`.
- `e707_times.txt`: the build time and peak memory of each module in the first build of the S707 modules, read by
  `repack.py`.
