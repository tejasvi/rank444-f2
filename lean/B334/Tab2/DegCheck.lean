import B334.Tab2.Deg
import B334.Tab2.Data
import B334.Tab2.DegData
import B334.E1x.Fact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The 288 degenerate rows of the class table (L5b), checked by the kernel

For each entry `(c, e, l, s, j, subs)` of `degRows`, `degOK` checks: `l` and `s` invertible (`isGL`), for every generator
`x` of `basisOf c ++ [e]` the image `actF l (invN s) x` is the XOR of the subset `subs` of `basisOf j`, the masks are
below 512, and `lbOf c ≤ lbOf j`. `rowValid_of_degOK` turns an accepted entry and `RowValid (basisOf j) (lbOf j)` into
`RowValid (basisOf c) (lbOf c)` (`rowValid_deg`, through `actA_toM3`: the statement's action on codes is `actF`). -/

namespace B334.Tab2

open B334 B334.Bind B334.E1x B334.Core

theorem toM3_mul_z (u v : Nat) :
    @HMul.hMul (Matrix (Fin 3) (Fin 3) (ZMod 2)) (Matrix (Fin 3) (Fin 3) (ZMod 2)) (Matrix (Fin 3) (Fin 3) (ZMod 2)) _
      (toM3 u) (toM3 v) = toM3 (mulF u v) :=
  (toM3_mulF u v).symm

/-- the statement's action on a 9-bit code is the code-level action `actF` -/
theorem actA_toM3 (p q x : Nat) :
    actA (toM3 p) (toM3 q) (vecOfMask (3 * 3) x) = vecOfMask (3 * 3) (actF p q x) := by
  unfold actA
  rw [mat3_vecOfMask, toM3_mul_z, toM3_mul_z]
  exact vecA_toM3 (actF p q x)

/-- the check of one degenerate entry -/
def degOK (d : Nat × Nat × Nat × Nat × Nat × List Nat) : Bool :=
  isGL d.2.2.1 && isGL d.2.2.2.1 &&
  ((basisOf d.1 ++ [d.2.1]).length == d.2.2.2.2.2.length) &&
  ((basisOf d.1 ++ [d.2.1]).zip d.2.2.2.2.2).all (fun g =>
    Nat.blt g.1 512 && (xorSub (basisOf d.2.2.2.2.1) g.2 == actF d.2.2.1 (invN d.2.2.2.1) g.1)) &&
  (basisOf d.2.2.2.2.1).all (fun b => Nat.blt b 512) &&
  Nat.ble (lbOf d.1) (lbOf d.2.2.2.2.1)

theorem mem_zip_left {α β : Type*} : ∀ (l : List α) (m : List β), l.length = m.length →
    ∀ x ∈ l, ∃ y, (x, y) ∈ l.zip m := by
  intro l
  induction l with
  | nil => intro m _ x hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro m hlen x hx
    cases m with
    | nil => simp at hlen
    | cons b m =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨b, by rw [h]; exact List.mem_cons_self⟩
      · obtain ⟨y, hy⟩ := ih m hlen x h
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-- **L5b for one entry.** -/
theorem rowValid_of_degOK (d : Nat × Nat × Nat × Nat × Nat × List Nat) (h : degOK d = true)
    (hj : RowValid (basisOf d.2.2.2.2.1) (lbOf d.2.2.2.2.1)) : RowValid (basisOf d.1) (lbOf d.1) := by
  obtain ⟨c, e, l, s, j, subs⟩ := d
  simp only [degOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨hl, hs⟩, hlen⟩, hgen⟩, hbj⟩, hlb⟩ := h
  have hP := gl_inv hl
  have hQ := gl_inv hs
  refine rowValid_deg (e := e) (toM3 l) (toM3 (invN s)) (toM3 (invN l)) (toM3 s) hP.1 hQ.2 ?_ hj hlb
  intro x hx
  obtain ⟨sub, hxs⟩ := mem_zip_left _ _ hlen x hx
  obtain ⟨_, hxy⟩ := hgen (x, sub) hxs
  rw [actA_toM3, ← hxy]
  exact xorSub_mem _ _

theorem degAll : degRows.all degOK = true := by decide +kernel

/-- every degenerate row is valid, given its target row -/
theorem deg_rows_valid : ∀ d ∈ degRows, RowValid (basisOf d.2.2.2.2.1) (lbOf d.2.2.2.2.1) →
    RowValid (basisOf d.1) (lbOf d.1) :=
  fun d hd hj => rowValid_of_degOK d (List.all_eq_true.mp degAll d hd) hj

end B334.Tab2
