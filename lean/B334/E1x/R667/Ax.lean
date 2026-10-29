import B334.E1x.R667.Fin
import B334.E1x.AxCheckT2

/-! # Axiom gate of the E1G run `R667`: standard axioms plus the T2 native-chunk axiom (`T2.nl_667`
records cover some of its leaves; `B334/E1x/AxCheckT2.lean`) -/

#assert_axioms_T2 B334.E1x.R667.run_667
#assert_axioms_T2 B334.E1x.R667.concl
#assert_axioms_T2 B334.E1x.R667.enum
