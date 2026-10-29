import B334.E1x.R619.F
import B334.E1x.R619.HT
import B334.E1x.GJ.JobS
import B334.E1x.R619.J9535

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `R619`, jobs 9605 … 9706: the generated Fin's job blocks r942 … r943 as
theorems (plain `decide` as `decide +kernel`), joined into `grpJ_12` -/

namespace B334.E1x.R619
open B334 B334.E1x B334.E1x.E1GS

theorem jrJ_942 : ∀ k, 9605 ≤ k → k < 9675 → JobOK C sl UB (HT.entry k) :=
  GJ.jobs_of_allR C sl UB UBR UB_eq UBR_eq UB_le HT.entry JL_9535 JW_9535 9605 70 jr_9605
theorem jrJ_943 : ∀ k, 9675 ≤ k → k < 9707 → JobOK C sl UB (HT.entry k) :=
  GJ.jobs_of_allR C sl UB UBR UB_eq UBR_eq UB_le HT.entry JL_9535 JW_9535 9675 32 jr_9675

theorem grpJ_12 : ∀ k, 9605 ≤ k → k < 9707 → JobOK C sl UB (HT.entry k) := by
  have a0 := jrJ_942
  have a1 := GJ.fa_join a0 jrJ_943
  exact a1

end B334.E1x.R619
