import B334.BCP.SemP

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The root records are the elimination of `T(X)`, checked by the kernel

Port of `S5/FactsRoot.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0). For every `X < 512` the precomputed root record
of BranchCheck334 (`rptP`, `rptPM`, `rkt`, `rlm`, `rrm`) is what the checker would compute from `T(X)` itself, and the
elimination of `T(X)` is accepted by `elimOk`. Four chunks of 128 functionals. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core

def rootOK (X : Nat) : Bool :=
  let s := elim (Nat.xor (txc24 X) ID24)
  Nat.beq (rptP X) s.P && Nat.beq (rptPM X) s.PM && Nat.beq (rlm X) (lmC s.P s.PM) && Nat.beq (rrm X) (kerM s.M) &&
  Nat.beq (rkt X) s.rk && elimOk s

theorem root_fact0 : allLT 128 (fun i => rootOK i) = true := by decide +kernel
theorem root_fact1 : allLT 128 (fun i => rootOK (128 + i)) = true := by decide +kernel
theorem root_fact2 : allLT 128 (fun i => rootOK (256 + i)) = true := by decide +kernel
theorem root_fact3 : allLT 128 (fun i => rootOK (384 + i)) = true := by decide +kernel

theorem root_fact (X : Nat) (hX : X < 512) : rootOK X = true := by
  by_cases h1 : X < 128
  · exact allLT_spec root_fact0 X h1
  by_cases h2 : X < 256
  · have := allLT_spec root_fact1 (X - 128) (by omega)
    rwa [show 128 + (X - 128) = X by omega] at this
  by_cases h3 : X < 384
  · have := allLT_spec root_fact2 (X - 256) (by omega)
    rwa [show 256 + (X - 256) = X by omega] at this
  · have := allLT_spec root_fact3 (X - 384) (by omega)
    rwa [show 384 + (X - 384) = X by omega] at this

end B334.BCP
