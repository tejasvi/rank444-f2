import B334.E1x.Fact
import B334.E1x.AxCheck

/-! Axiom gate for the G₀ action and the row facts of the E1 port (not part of the library). -/

#assert_std_axioms B334.E1x.toM3_mulF
#assert_std_axioms B334.E1x.gl_inv
#assert_std_axioms B334.E1x.actF_xor
#assert_std_axioms B334.E1x.actF_inj
#assert_std_axioms B334.E1x.isDecomp_left
#assert_std_axioms B334.E1x.isDecomp_mid
#assert_std_axioms B334.E1x.isDecomp_actF
#assert_std_axioms B334.E1x.actF_nz
#assert_std_axioms B334.E1x.fact_mono
#assert_std_axioms B334.E1x.fact_factN
#assert_std_axioms B334.E1x.fact_actF
#assert_std_axioms B334.E1x.T334_of_isDecomp
#assert_std_axioms B334.E1x.isDecomp_of_T334
#assert_std_axioms B334.E1x.fact_of_quotLB
#assert_std_axioms B334.E1x.quotLB_of_fact
