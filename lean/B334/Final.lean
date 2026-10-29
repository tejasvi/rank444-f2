import B334.Lem.TwoCase
import B334.Lem.Split
import B334.Lem.Orbit
import B334.Lem.Chain
import B334.E1x.Bridge
import B334.Tab2.Induct

/-! # The main theorems, from the two computed point bounds

The lemma layer (`B334/Lem/`) turns the two point bounds `QuotLB T334 P707 26` and
`QuotLB T334 P708 26` into R_F₂(⟨3,3,4⟩) ≥ 27, and the chain gives R_F₂(⟨3,4,4⟩) ≥ 31 and
R_F₂(⟨4,4,4⟩) ≥ 35. The point bounds come from the E1P runs of P707R2b and P708R2 through `quotLB_of_e1`
(`E1x/Bridge.lean`); `point707_of_e1`/`point708_of_e1` state that step, and the E1 runs themselves are assembled elsewhere.
`rank444_ge_35_of_runs` is the whole reduction: what is left is the E1 production, the 367 class runs
(`Tab2.RunHyp`, each run given the higher-dimensional classes) and the two point runs (given the class facts). -/

namespace B334

open B334.E1x B334.Bind

/-- R_F₂(⟨3,3,4⟩) ≥ 27 from the two point bounds -/
theorem rank334_ge_27_of (h707 : QuotLB T334 P707 26) (h708 : QuotLB T334 P708 26) : Rank334 :=
  B334.Lem.two_case B334.Lem.split_flattening sym334 B334.Lem.point_orbit2 B334.Lem.point_orbit3 h707 h708

theorem rank344_ge_31_of (h707 : QuotLB T334 P707 26) (h708 : QuotLB T334 P708 26) : Rank344 :=
  B334.Lem.chain344 B334.Lem.chain_step B334.Lem.cyclic (rank334_ge_27_of h707 h708)

theorem rank444_ge_35_of (h707 : QuotLB T334 P707 26) (h708 : QuotLB T334 P708 26) : Rank444 :=
  B334.Lem.chain444 B334.Lem.chain_step B334.Lem.cyclic (rank344_ge_31_of h707 h708)

/-- the P707 bound from an E1 run on its IP (point mask `m`, 25 outside terms refuted) -/
theorem point707_of_e1 {m X : Nat} (hE : E1Concl m 25) (h1 : oneOK m X = true) (hm : emOK m [10] = true) :
    QuotLB T334 P707 26 := by
  rw [p707_eq]; exact quotLB_of_e1 (by decide) hE h1 hm

/-- the P708 bound from an E1 run on its IP -/
theorem point708_of_e1 {m X : Nat} (hE : E1Concl m 25) (h1 : oneOK m X = true) (hm : emOK m [84] = true) :
    QuotLB T334 P708 26 := by
  rw [p708_eq]; exact quotLB_of_e1 (by decide) hE h1 hm

/-- the class facts the point IPs use (`Tab2.hcls_all`) -/
abbrev ClassFacts : Prop :=
  ∀ c, c < Tab2.nCls → Tab2.lbOf c ≠ 0 → RowValid (Tab2.basisOf c) (Tab2.lbOf c)

/-- **The reduction to the E1 production.** R_F₂(⟨3,3,4⟩) ≥ 27 from the 367 class runs (`Tab2.RunHyp`) and the two
point runs, each point run given the class facts. -/
theorem rank334_ge_27_of_runs (hrun : Tab2.RunHyp) (h707 : ClassFacts → QuotLB T334 P707 26)
    (h708 : ClassFacts → QuotLB T334 P708 26) : Rank334 :=
  rank334_ge_27_of (h707 (Tab2.hcls_all hrun)) (h708 (Tab2.hcls_all hrun))

theorem rank344_ge_31_of_runs (hrun : Tab2.RunHyp) (h707 : ClassFacts → QuotLB T334 P707 26)
    (h708 : ClassFacts → QuotLB T334 P708 26) : Rank344 :=
  rank344_ge_31_of (h707 (Tab2.hcls_all hrun)) (h708 (Tab2.hcls_all hrun))

theorem rank444_ge_35_of_runs (hrun : Tab2.RunHyp) (h707 : ClassFacts → QuotLB T334 P707 26)
    (h708 : ClassFacts → QuotLB T334 P708 26) : Rank444 :=
  rank444_ge_35_of (h707 (Tab2.hcls_all hrun)) (h708 (Tab2.hcls_all hrun))

end B334
