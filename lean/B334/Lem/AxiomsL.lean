import B334.E1x.AxCheck
import B334.Lem.Orbit
import B334.Lem.Split
import B334.Lem.TwoCase
import B334.Lem.Chain
import B334.Lem.SanityL

/-! Axiom census for the lemma layer (`B334/Lem`; not part of the library). `#assert_std_axioms`
(`E1x/AxCheck.lean`) fails the compile unless the axioms are exactly among propext, Classical.choice and Quot.sound, so
a successful compile is the census; `#print axioms` keeps the record in the log. -/

#print axioms B334.Lem.point_orbit2
#print axioms B334.Lem.point_orbit3
#print axioms B334.Lem.rk3_eq
#print axioms B334.Lem.split_flattening
#print axioms B334.Lem.two_case
#print axioms B334.Lem.chain_step
#print axioms B334.Lem.cyclic
#print axioms B334.Lem.chain344
#print axioms B334.Lem.chain444
#print axioms B334.Lem.rankLE_29
#print axioms B334.Lem.rankLE_naive
#print axioms B334.Lem.trace_identity

#assert_std_axioms B334.Lem.point_orbit2
#assert_std_axioms B334.Lem.point_orbit3
#assert_std_axioms B334.Lem.rk3_eq
#assert_std_axioms B334.Lem.rank_vecOfMask
#assert_std_axioms B334.Lem.wit_all
#assert_std_axioms B334.Lem.split_flattening
#assert_std_axioms B334.Lem.rank_splitF_T334
#assert_std_axioms B334.Lem.rank_sum_le
#assert_std_axioms B334.Lem.two_case
#assert_std_axioms B334.Lem.chain_step
#assert_std_axioms B334.Lem.cyclic
#assert_std_axioms B334.Lem.chain344
#assert_std_axioms B334.Lem.chain444
#assert_std_axioms B334.Lem.rankLE_29
#assert_std_axioms B334.Lem.nv1_check
#assert_std_axioms B334.Lem.rankLE_naive
#assert_std_axioms B334.Lem.trace_identity

/-- the pieces compose: L1, L3a, L3b and the two point bounds give R(⟨3,3,4⟩) ≥ 27 -/
example (h707 : B334.QuotLB B334.T334 B334.P707 26) (h708 : B334.QuotLB B334.T334 B334.P708 26) : B334.Rank334 :=
  B334.Lem.two_case B334.Lem.split_flattening B334.sym334 B334.Lem.point_orbit2 B334.Lem.point_orbit3 h707 h708

/-- the chain composes: R(⟨3,3,4⟩) ≥ 27 gives R(⟨4,4,4⟩) ≥ 35 -/
example (h334 : B334.Rank334) : B334.Rank444 :=
  B334.Lem.chain444 B334.Lem.chain_step B334.Lem.cyclic (B334.Lem.chain344 B334.Lem.chain_step B334.Lem.cyclic h334)
