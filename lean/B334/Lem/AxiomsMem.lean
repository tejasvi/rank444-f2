import B334.E1x.AxCheck
import B334.Tables.SymFacts
import B334.MethodK.Rows.R16
import B334.MethodK.Rows.R135
import B334.MethodK.Rows.R147

/-! Axiom gate for the memory split (not part of the library): the table facts rebuilt from their
range parts (`Tables/Split`) and the rows 16, 135, 147 with K-W chunks of 64
masks. `#assert_std_axioms` (`E1x/AxCheck.lean`) fails the compile on any axiom beyond propext, Classical.choice and
Quot.sound. -/

#assert_std_axioms B334.Tab.wc_fact_1
#assert_std_axioms B334.Tab.wc_fact_16
#assert_std_axioms B334.Tab.wc_fact_17
#assert_std_axioms B334.Tab.wc_fact_18
#assert_std_axioms B334.Tab.wc_fact_256
#assert_std_axioms B334.Tab.wc_fact_257
#assert_std_axioms B334.Tab.wc_fact_258
#assert_std_axioms B334.Tab.wc_fact_272
#assert_std_axioms B334.Tab.wc_fact_273
#assert_std_axioms B334.Tab.wc_fact_274
#assert_std_axioms B334.Tab.wc_fact_288
#assert_std_axioms B334.Tab.wc_fact_289
#assert_std_axioms B334.Tab.wc_fact_290
#assert_std_axioms B334.Tab.wc_fact_291
#assert_std_axioms B334.Tab.wc_fact_292
#assert_std_axioms B334.Tab.orbm_fact
#assert_std_axioms B334.Tab.wb_fact
#assert_std_axioms B334.Tab.wb_exists
#assert_std_axioms B334.Tab.wc_exists
#assert_std_axioms B334.MethodK.R16.row
#assert_std_axioms B334.MethodK.R135.row
#assert_std_axioms B334.MethodK.R147.row
