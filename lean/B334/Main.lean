import B334.MainRun
import B334.E1x.Pts.S708.Fin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The main theorems (closing module)

R_F₂(⟨3,3,4⟩) ≥ 27, R_F₂(⟨3,4,4⟩) ≥ 31 and R_F₂(⟨4,4,4⟩) ≥ 35, as stated in `B334/Statement.lean`.

* `B334.classFacts` and `B334.quot707` (`B334/MainRun.lean`): the 367 E1G runs give every class fact, and the
  point-707 run then gives `QuotLB T334 P707 26`.
* `B334.E1x.Pts.S708.h708`: the point-708 run, given the class facts.
* `rank334_ge_27_of` and the chain (`B334/Final.lean`) assemble them with the lemma layer.

The three theorems below combine these facts. -/

namespace B334

/-- **R_F₂(⟨3,3,4⟩) ≥ 27.** -/
theorem rank334_ge_27 : Rank334 := rank334_ge_27_of quot707 (B334.E1x.Pts.S708.h708 classFacts)

/-- **R_F₂(⟨3,4,4⟩) ≥ 31.** -/
theorem rank344_ge_31 : Rank344 := rank344_ge_31_of quot707 (B334.E1x.Pts.S708.h708 classFacts)

/-- **R_F₂(⟨4,4,4⟩) ≥ 35.** -/
theorem rank444_ge_35 : Rank444 := rank444_ge_35_of quot707 (B334.E1x.Pts.S708.h708 classFacts)

end B334

#print axioms B334.rank334_ge_27
#print axioms B334.rank344_ge_31
#print axioms B334.rank444_ge_35
