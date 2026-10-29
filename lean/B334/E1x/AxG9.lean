import B334.E1x.RB.RunsAll3
import B334.E1x.AxCheckT2

/-! Axiom gate for the run theorems of all E1G runs (not part of the library): standard axioms plus the T2
native-chunk axiom (the runs of 613, 615, 618, 619, 663, 665, 667, 682 use `T2.nl_<c>` records). -/

#assert_axioms_T2 B334.E1x.RBRuns3.runsAll
