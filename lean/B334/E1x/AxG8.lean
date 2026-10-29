import B334.E1x.RB.RunsAll2
import B334.E1x.AxCheckT2

/-! Axiom gate for the run theorems of the simple and the single-trace leaf E1G runs (not part of the library):
standard axioms plus the T2 native-chunk axiom (the runs of 613, 615, 663, 665 use `T2.nl_<c>` records). -/

#assert_axioms_T2 B334.E1x.RBRuns2.runsAll
