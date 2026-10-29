import B334.E1x.Pad
import B334.Bind.Span

/-! # From an E1 run to `QuotLB`

An E1 run on a run's IP concludes `E1Concl m R` for the IP's point mask `m`. With a hyperplane witness `X` over `m`
(`oneOK`, so `Fact m 1`) padding gives `Fact m (R + 1)`; when `m` is the point mask of `spanMasks B` (`emOK`, one loop
over the 512 masks) this is `QuotLB T334 (spanMasks B) (R + 1)`, i.e. `RowValid B (R + 1)`. The proof keeps
the decomposition of `T` throughout (QuotLB form). The two point subspaces of the statement are `spanMasks [10]`
and `spanMasks [84]`. -/

namespace B334.E1x

open B334.Core B334.Bind

/-- `m` is the point mask of `spanMasks B` below 512 -/
def emOK (m : Nat) (B : List Nat) : Bool := allLT 512 (fun w => m.testBit w == inSpan B w)

theorem em_spec {m : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < 2 ^ 9) (h : emOK m B = true) :
    ∀ w < 512, m.testBit w = true ↔ vecOfMask (3 * 3) w ∈ spanMasks B := by
  intro w hw
  have := allLT_spec h w hw
  rw [beq_iff_eq] at this
  rw [this, mem_spanMasks_iff B hB w (by omega)]

theorem p707_eq : P707 = spanMasks [10] := by
  unfold P707 spanMasks
  congr 1
  ext v
  simp [eq_comm]

theorem p708_eq : P708 = spanMasks [84] := by
  unfold P708 spanMasks
  congr 1
  ext v
  simp [eq_comm]

/-- **From an E1 run to `QuotLB`.** An E1 refutation of "exactly `R` first factors outside `m`", a hyperplane over `m`, and
`m` = the point mask of `spanMasks B` give `QuotLB T334 (spanMasks B) (R + 1)`. -/
theorem quotLB_of_e1 {B : List Nat} {m R X : Nat} (hB : ∀ b ∈ B, b < 2 ^ 9) (hE : E1Concl m R)
    (h1 : oneOK m X = true) (hm : emOK m B = true) : QuotLB T334 (spanMasks B) (R + 1) :=
  quotLB_of_fact (pad hE (fact_one' h1)) (em_spec hB hm)

theorem rowValid_of_e1 {B : List Nat} {m R X : Nat} (hB : ∀ b ∈ B, b < 2 ^ 9) (hE : E1Concl m R)
    (h1 : oneOK m X = true) (hm : emOK m B = true) : RowValid B (R + 1) :=
  quotLB_of_e1 hB hE h1 hm

end B334.E1x
