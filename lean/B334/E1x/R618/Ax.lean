import B334.E1x.R618.Fin
import B334.E1x.AxCheckT2

/-! # Axiom gate of the E1G run `R618`: standard axioms plus the T2 native-chunk axiom (`T2.nl_618`
records cover some of its leaves; `B334/E1x/AxCheckT2.lean`) -/

#assert_axioms_T2 B334.E1x.R618.run_618
#assert_axioms_T2 B334.E1x.R618.concl
#assert_axioms_T2 B334.E1x.R618.enum
