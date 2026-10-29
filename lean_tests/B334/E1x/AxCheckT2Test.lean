import B334.E1x.AxCheckT2
import B334.T2.N_0

/-! # Tests of the T2 axiom gate `#assert_axioms_T2` (not part of the library)

Negative: a theorem on a declared axiom and a theorem proved by another `native_decide` are rejected. Positive: the
native-chunk fact `T2.nl_619_ok` (the one allowed extra axiom) and standard-axiom theorems pass. -/

namespace B334.E1x.AxCheckT2Test

/-- an axiom outside the trust base (this test module only) -/
axiom badAx : (1 : Nat) = 2

theorem usesBad : (1 : Nat) = 2 := badAx

/-- another native-decide axiom: not the T2 one -/
theorem usesOtherNative : (2 : Nat) + 2 = 4 := by native_decide

theorem usesStd : ∀ p : Prop, p ∨ ¬p := Classical.em

#expect_T2_gate_failure usesBad
#expect_T2_gate_failure usesOtherNative
#assert_axioms_T2 B334.T2.nl_619_ok
#assert_axioms_T2 usesStd

end B334.E1x.AxCheckT2Test
