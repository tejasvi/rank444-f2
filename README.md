# B334: a Lean 4 certificate for R_F₂(⟨3,3,4⟩) ≥ 27, R_F₂(⟨3,4,4⟩) ≥ 31, R_F₂(⟨4,4,4⟩) ≥ 35

This repository holds the Lean proof and the search programs for the paper *The rank of 4×4 matrix multiplication
over F₂ is at least 35* (T. S. Tomar, doi:10.5281/zenodo.23749576). It contains the unpacked `B334-lean.zip` and
`B334-search.zip` from version 1.1 of the Zenodo archive (doi:10.5281/zenodo.23761132; all versions:
doi:10.5281/zenodo.23749573). `B334-lean.zip` is unchanged since version 1.0, and this README replaces the version 1.0
README inside it.

- `lean/`: the Lean 4 proof; `lean_tests/`: its test modules;
- `MODULES.txt`, `layers.txt`, `TESTS.txt`, `tests_layers.txt`, `DATA_FILES.tsv`, `DATA_SHA256SUMS` and
  `DATA_SHA256SUMS_TESTS`: the lists of modules and data files, with the checksums of the data files;
- `ops/`: the build and check scripts;
- `search/`: the programs that made the data files and the generated modules;
- `LICENSE`: the Apache License 2.0.

The data files and `evidence/` are not in the repository. `evidence/` has the logs and outputs of the reference build
and of the checks, and some of the scripts, programs and probe modules that produced them; the build scripts and the
name scan are in `ops/`. Download `B334-data.tar.zst`, `B334-runs.tar.zst`, `B334-data707.tar.zst` and
`B334-evidence.tar.zst` from the GitHub release v1.1 or from Zenodo, set `DL` to the download directory, then run this
from the repository root:

```
for a in data runs data707 evidence; do zstd -dc "$DL/B334-$a.tar.zst" | tar -xf -; done
```

This puts `data/`, `data707/`, `runs/` and `evidence/` next to `lean/`. The Lean modules read the first three as
`../data/`, `../data707/` and `../runs/`; the build does not need `evidence/`. The release also has `MANIFEST.md`,
which describes every file of the archive, and `SHA256SUMS`, which lists their checksums.

## What is proved

`B334/Statement.lean` states the claims as plain definitions over `ZMod 2`. Its sha256 is
`ec6b34bde2da323fa4fe47c44529fb0ea59e63535cb15435257624ccde46c742`.

- `RankLE T r` says that the tensor `T` is a sum of `r` rank-one tensors, zero terms allowed. So `¬ RankLE T r` says
  that `T` has rank at least `r + 1`.
- `mmT n m p` is the matrix multiplication tensor ⟨n,m,p⟩.
- `Rank334 := ¬ RankLE T334 26`, where `T334 := mmT 3 3 4`; `Rank344 := ¬ RankLE (mmT 3 4 4) 30`;
  `Rank444 := ¬ RankLE (mmT 4 4 4) 34`.

In the docstring of Statement.lean, "the paper" means arXiv:2603.07280, whose §3.3 displays the third factor as (i,k);
Statement.lean and Wang's code use (k,i).

`B334/Main.lean` proves:

```lean
theorem B334.rank334_ge_27 : Rank334
theorem B334.rank344_ge_31 : Rank344
theorem B334.rank444_ge_35 : Rank444
```

## Trust base

`#print axioms` reports the same list for each of the three theorems:

```
[propext, Classical.choice, Quot.sound, B334.T2.nat_ok._native.native_decide.ax_1_1]
```

The first three are Lean's standard axioms. The fourth comes from the only use of `native_decide`, in
`B334/T2/N_0.lean`. It covers 811 of the 19,562 completion-leaf certificates, which belong to 8 classes of
3-dimensional subspaces: for these 811, the certificate checker `B334.BC.leafS` is evaluated by Lean's compiler and
evaluator instead of the kernel. The kernel runs the same checker on the other 18,751 certificates and checks its
soundness theorem, `B334.BCP.leafS_sound`.

Native evaluation is used for them because they try the most candidates: each of them tries more than 500, 513 of
them more than 1,000, and the largest 78,379. Kernel probes on certificates with 169 to 2,853 candidate tries measured
about 4–8 MiB of memory for each candidate tried. A cost model calibrated on 8 module builds predicts that 490 of these
811 leaves, all among the 513 with more than 1,000 tries, would need more than 7,600 MiB each under the kernel (the
limit, `-M 7600`, for which the kernel modules of the other certificates were sized), and the largest about 542
GiB; the model over-predicted all of its calibration builds, so these figures are likely overestimates. A possible
follow-up is to check them with the kernel alone, which would need a different checker design or up to about 0.53 TiB
of memory per leaf. `evidence/kernel_cost/` holds the counts, the memory probes and the cost model behind these
figures.

Compiled into a standalone program by the same Lean compiler, the checker accepted all 19,543 certificates that existed
when this test was run; the 19 added later are among those checked by the kernel. On 2,150 mutated certificates, 53
of which are still valid, its verdicts agree with those of an independently written checker. The records of both
tests are in `evidence/native_check/`.

Everything else is checked by the kernel: the lemmas, the class table and the search replays.

## How the proof is organised

- The two-case argument (`B334/Lem/TwoCase.lean`) reduces ⟨3,3,4⟩ ≥ 27 to two bounds, `QuotLB T334 P707 26` and
  `QuotLB T334 P708 26`, one for each "point": the subspaces spanned by a matrix of rank 2 and by a matrix of rank 3.
  The chain lemmas then give ⟨3,4,4⟩ and ⟨4,4,4⟩.
- Each point bound is a kernel-checked replay of a recorded branch-and-bound search:
  - `B334/E1x/Pts/S707`, `B334/E1x/Pts/S708`: the search blocks and the coverage of every delegated subtree (computed
    from the replayed records rather than from the presence of files); `B334/E1x/Pts/H707`, `H708`: the slot tables
    of the row inequalities.
- The row inequalities come from a table of 710 subspace classes (`B334/Tab2`). It is proved by induction on
  dimension, from direct certificates, degenerate and monotone rows, and 367 further search replays. These are in
  `B334/E1x/R<c>`, except that six of the fifteen for 2-dimensional subspaces are in `B334/E1x/I<c>`.
- Each search leaf is matched to its certificate record by an explicit permutation of its terms
  (`B334/BCP/PermL.lean`).

## Building

- **Toolchain.** Lean 4.30.0, as installed by elan for `leanprover/lean4:v4.30.0` (commit
  `d024af099ca4bf2c86f649261ebf59565dc8c622`). The kernel and the rest of Lean are in `lib/lean/libleanshared.so`,
  sha256 `86c5222603b164cd1c0dee1aeea9624a1ece9ce724ee2ed36e427a4259f8834b`; the `bin/lean` launcher has sha256
  `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf`. Mathlib v4.30.0, commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`. `evidence/toolchain_record.txt` lists these hashes and the revisions of
  Mathlib's dependencies.
- **Modules.** 42,559, listed in `MODULES.txt`, built in the order of `layers.txt`, each with `lean -j1`.
- **Memory.** The reference build used `-M 15000` (14.6 GiB) for every module except those under `B334/E1x/Pts/S707`
  and `B334/Main`, which used `-M 18000` (17.6 GiB) from the start. The largest peak was 14.8 GiB, for
  `B334/E1x/Pts/S707/K298C4`: more than the 14.6 GiB of `-M 15000`, at which it failed in two earlier builds of the
  same code. Three other `B334/E1x/Pts/S707` modules peaked at 14.4–14.5 GiB, and `B334/Main` at 13.9 GiB. For a
  rebuild we recommend the same two limits, with 18 GiB of memory for each module built with `-M 18000`.
- **Cost.** About 119 core-hours of CPU time for one build of every module. The reference build took 4 h 14 min of
  wall time, with at most 38 modules building at a time.
- **Preemption.** The reference build ran on a spot machine, which was preempted once, at about 17:44Z on 2026-10-28,
  after 38,575 modules had built. The build was resumed in the same tree with the same settings. Lean does not
  re-check imported `.olean` files, so the second pass rebuilt every module without an `rc=0` line in the first
  pass's `times.txt` (3,984) and every other module whose `.olean` had been written in the last 5 minutes of the first
  pass (792), 4,776 modules in all, with no failure. All the checks below ran on the final tree.
- **Records.** `evidence/build/` holds the status files and the per-module times and peak memory of both passes, the
  list of the modules the second pass rebuilt with the 5-minute cut that chose them, and the `times.txt` lines of the
  two earlier K298C4 failures.

## Data files

Large literals (search blocks, slot tables) are read at elaboration time by the commands `#e1lits` and `#rttablew`
(`B334/E1x/Load.lean`). The paths are relative to the directory `lean` runs in: `../data/<f>`, `../data707/<f>` and
`../runs/<tag>/<f>`. There are 17,809 such files, 4.21 GiB in all.

Known limitation: data files are read by relative path, without a content pin. DATA_SHA256SUMS lists them. A wrong
file can at worst make the build fail. It cannot make a false theorem pass. A content-hash pin per file is planned for
a later version.

Every declaration the loader adds is an ordinary definition (`defnDecl`), so none of them is an axiom. The kernel
checks each of them, and also checks the three main theorems against the statements in `B334/Statement.lean`.

## Checks that come with the release

`evidence/checks/` holds the reference build's axiom census results and its logs of the `autoImplicit` check and of
the test target.

- The axiom census: the 392 `#print axioms` results in the census modules are all subsets of the trust base above.
  In addition, 176 gates (`#assert_std_axioms`, `#assert_axioms_T2`) stop the build if a declaration depends on an
  axiom outside its allowed list.
- `ops/name_scan.sh` finds no `sorry`, `admit`, axiom declaration, `implemented_by`, `extern`, `unsafe` or `opaque` in
  the release modules, and `native_decide` only in `B334/T2/N_0`. Its output for the release is
  `evidence/name_scan.out`, which prints one exemption: the axiom gate's allow-list line in the release module
  `B334/E1x/AxCheckT2`, which names the allowed axiom. The gate's negative test, in the test target, is exempt as a
  whole module.
- The statement files (`Statement`, `Final`, the two point modules, `MainRun`, `Main`) elaborate with `autoImplicit`
  and `relaxedAutoImplicit` off; the other modules are built with the default flags.
- A separate test target, `lean_tests/` with 83 modules, builds against the release, but no release module imports
  it. It holds negative controls, in which mutated certificates are rejected, and a negative test of the axiom gate.
- The build logs of the 6,988 job modules that load literals with `#e1lits` (`B334/E1x/Pts/S70x/J*` and
  `B334/E1x/R<c>/J*`) contain a `PANIC` message with a backtrace from Lean's code generator
  (`Lean.Compiler.LCNF.ExplicitBoxing`, "unreachable code has been reached"), printed while it tries to compile the
  definitions that read the loaded literals. These definitions are in a `noncomputable section`, the modules build
  (`rc=0`), and their theorems are proved by `decide +kernel`, which the kernel evaluates. The one compiled evaluation,
  in `B334/T2/N_0`, imports none of these modules, and its log has no such message. So no proof depends on code
  compiled from these modules.

## The programs

`search/` (in `B334-search.zip`) holds the programs that built the search instances, ran the searches, wrote and
checked the certificates, computed the class table, and turned the results into the data files and generated modules
of this archive. `search/README.md` gives the role of each program and its section of the paper, the build, the
commands of the original runs with their running times, and how to compare files made again with `DATA_SHA256SUMS`
and with the list of the release sources. The programs were built again for this version and rerun on a sample of the
original runs: the files they wrote equal those of the archive, with the exceptions that `search/README.md` explains.

## How to cite

Please cite the paper, and this archive if you use the formalization, its data or its programs:

- Tejasvi Singh Tomar. The rank of 4×4 matrix multiplication over F2 is at least 35. Zenodo, 2026. doi:10.5281/zenodo.23749576.
- Tejasvi Singh Tomar. Lean 4 proof that the rank of 4×4 matrix multiplication over F2 is at least 35. Zenodo, 2026. doi:10.5281/zenodo.23761132 (version 1.1; all versions: doi:10.5281/zenodo.23749573).

## License

The code (`lean/`, `lean_tests/`, the shell scripts in `ops/`, the scripts, programs and probe modules in `evidence/`,
and the programs in `search/`) is licensed under the Apache License 2.0, and the data files, the documentation and the
records (logs, lists and hash files) are licensed under CC-BY-4.0. The full text of the Apache License 2.0 is in
`LICENSE`. Some data of the class table come from Wang's certificate files (MIT license); the license notice is in
`search/inputs/WANG-LICENSE.txt`.

Some modules are ported from `rank333-f2`, the Lean release of the proof that R_F₂(⟨3,3,3⟩) = 23
(doi:10.5281/zenodo.23236154), which is also licensed under Apache-2.0:

- `B334/BC/BranchCheck334`;
- in `B334/BCP/`: `Base`, `Bit`, `Check`, `CheckC`, `Count`, `Elim`, `ElimLA`, `Enum`, `Leaf`, `Masks`, `Rec`, `Root`,
  `Sem`, `SemP` and `Sym`;
- in `B334/Core/`: `Branch334`, `LinAlg`, `Sym334`, `SymBits`, `Tensor334` and `Terms334`;
- in `B334/E1x/`: `Act`, `CheckG`, `CheckP`, `Decomp`, `Fact`, `GLTab`, `IPChk`, `Load`, `Pad`, `RT9`, `RTE`, `SlotG`,
  `SlotP`, `TabG`, `TabP`, `TransBits`, and `Bridge1`, `Bridge2` and `Bridge3` in both `G/` and `P/`.

The header of each of these modules names the files it comes from and what changed. Some programs in `search/` derive
from programs of `rank333-f2` as well; `search/README.md` lists them.
