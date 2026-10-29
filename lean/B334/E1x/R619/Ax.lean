import B334.E1x.R619.Fin
import B334.E1x.AxCheckT2

/-! # Axiom gate of the E1G run `R619`: standard axioms plus the T2 native-chunk axiom (`T2.nl_619`
records cover some of its leaves; `B334/E1x/AxCheckT2.lean`) -/

#assert_axioms_T2 B334.E1x.R619.run_619
#assert_axioms_T2 B334.E1x.R619.concl
#assert_axioms_T2 B334.E1x.R619.enum
