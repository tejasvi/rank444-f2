import B334.E1x.P.Hdr
import B334.E1x.Pts.ChkB

/-! # From the core Boolean checks to the composition hypotheses

* `blk_eq`, `glueChk_eq`, `glueChkW_eq`: `blkChk`, `glueChk`, `glueChkW` (`P/Asm.lean`, `P/Hdr.lean`) as
  `IPChk.allR` loops over the core checks of `Pts/ChkB.lean`, so that ranges checked in separate core modules join by
  `IPChk.allR_join`.
* `jobB_sound`: an accepted job check gives `JobOK` of the job's header (its chain from `chain_sound`, its header by
  `jobOK_hdr0`); `jobs_of_allR` for a range of jobs; `fa_join` joins ranges. -/

set_option maxRecDepth 20000
set_option exponentiation.threshold 1300
namespace B334.E1x.Pts
open B334.E1x.E1PS

/-- a conjunction loop from 0 is `IPChk.allR` from 0 -/
theorem rec_and_allR (f : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun i b => b && f i) n =
    IPChk.allR f 0 n
  | 0 => rfl
  | n + 1 => by
    show (Nat.rec (motive := fun _ => Bool) true (fun i b => b && f i) n && f n) = (IPChk.allR f 0 n && f (0 + n))
    rw [rec_and_allR f n, Nat.zero_add]

theorem blk_eq (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (L : List ℕ) (a m : ℕ) :
    blkChk C sl UB UBR L a m = IPChk.allR (fun i => E1P.block C sl UB UBR (L.getD i 0)) a m := rfl

theorem glueChk_eq (L : List ℕ) (W : List (List ℕ)) : glueChk L W = IPChk.allR (glueIB L W) 0 L.length :=
  rec_and_allR (glueIB L W) L.length

theorem glueChkW_eq (Ss : List ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ) :
    glueChkW Ss nJ Jf Wf = IPChk.allR (glueWB Ss nJ Jf Wf) 0 Ss.length :=
  rec_and_allR (glueWB Ss nJ Jf Wf) Ss.length

/-- **A job from its parts**: its pieces pass, its records are glued inside, and its first piece is a mode-0 block
with header `H` (the parts may come from several check modules, joined by `IPChk.allR_join`). -/
theorem jobOK_of_parts (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (hUB : UB = V (fun l => E1P.fld UB l))
    (hUBR : UBR = VR (fun l => E1P.fld UB l)) (hubb : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32)
    (H : ℕ) (L : List ℕ) (W : List (List ℕ)) (h0 : 0 < L.length)
    (hb : IPChk.allR (fun i => E1P.block C sl UB UBR (L.getD i 0)) 0 L.length = true)
    (hg : IPChk.allR (glueIB L W) 0 L.length = true) (hm0 : L.getD 0 0 % 2 = 0)
    (hS : H = L.getD 0 0 % 2 ^ (14 + 8 * (L.getD 0 0 / 2 % 2 ^ 5))) : JobOK C sl UB H := by
  have hblk : ∀ i < L.length, E1P.block C sl UB UBR (L.getD i 0) = true :=
    blkChk_spec C sl UB UBR L L.length (by rw [blk_eq]; exact hb)
  have hgl : glueChk L W = true := by rw [glueChk_eq]; exact hg
  rw [hS]
  exact (jobOK_hdr0 C sl UB (L.getD 0 0) hm0).mpr (fun x hg' hsl hxub hx =>
    chain_sound C sl UB UBR (fun l => E1P.fld UB l) x hg' hsl hUB hUBR hubb hxub hx L hblk
      (glueChk_spec L W hgl) 0 h0)

/-- **An accepted job check gives the job's `JobOK`.** -/
theorem jobB_sound (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (hUB : UB = V (fun l => E1P.fld UB l))
    (hUBR : UBR = VR (fun l => E1P.fld UB l)) (hubb : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32)
    (H : ℕ) (L : List ℕ) (W : List (List ℕ)) (h : jobB C sl UB UBR H L W = true) : JobOK C sl UB H := by
  unfold jobB at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h0, hb⟩, hg⟩, hm⟩, hH⟩ := h
  exact jobOK_of_parts C sl UB UBR hUB hUBR hubb H L W h0 hb hg (Nat.eq_of_beq_eq_true hm)
    (Nat.eq_of_beq_eq_true hH)

/-- a range of accepted job checks -/
theorem jobs_of_allR (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (hUB : UB = V (fun l => E1P.fld UB l))
    (hUBR : UBR = VR (fun l => E1P.fld UB l)) (hubb : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32)
    (HT : ℕ → ℕ) (JL : ℕ → List ℕ) (JW : ℕ → List (List ℕ)) (a m : ℕ)
    (h : IPChk.allR (fun k => jobB C sl UB UBR (HT k) (JL k) (JW k)) a m = true) :
    ∀ k, a ≤ k → k < a + m → JobOK C sl UB (HT k) := fun k h1 h2 => by
  have e := IPChk.allR_spec _ a m h (k - a) (by omega)
  rw [Nat.add_sub_cancel' h1] at e
  exact jobB_sound C sl UB UBR hUB hUBR hubb (HT k) (JL k) (JW k) e

/-- two adjacent ranges -/
theorem fa_join {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ k, a ≤ k → k < b → P k) (h2 : ∀ k, b ≤ k → k < c → P k) :
    ∀ k, a ≤ k → k < c → P k := fun k ha hc => if hb : k < b then h1 k ha hb else h2 k (by omega) hc

end B334.E1x.Pts
