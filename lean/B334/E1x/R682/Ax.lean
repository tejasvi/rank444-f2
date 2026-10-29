import B334.E1x.R682.Fin
import B334.E1x.AxCheckT2

/-! # Axiom gate of the E1G run `R682`: standard axioms plus the T2 native-chunk axiom (`T2.nl_682`
records cover some of its leaves; `B334/E1x/AxCheckT2.lean`) -/

#assert_axioms_T2 B334.E1x.R682.run_682
#assert_axioms_T2 B334.E1x.R682.concl
#assert_axioms_T2 B334.E1x.R682.enum
