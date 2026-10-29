import B334.Tab2.Direct
import B334.Tab2.DegCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The class table by induction on dimension (hcls)

Every class the point IPs use is valid at the bound they use: `hcls_all`. Its one hypothesis, `RunHyp`, is what the
E1 runs provide: a class on an E1 route (Route B, lifted, raised; `routeOf c = 2`) is valid once every strictly
higher-dimensional class is (an IP's rows are strict superspaces of its E). The other routes are proven here: direct
certificates (`direct_ok`) and degenerate or monotone rows (`deg_rows_valid`, whose targets have larger dimension).
The route data cover every class (kernel checks `cover_*`, `deg_dim`), and a class with no route has `lbOf c = 0`. -/

namespace B334.Tab2

open B334

def dimOf (c : Nat) : Nat := (basisOf c).length

/-- what the E1 runs must provide -/
def RunHyp : Prop :=
  ∀ c, c < nCls → routeOf c = 2 → lbOf c ≠ 0 →
    (∀ c', c' < nCls → dimOf c < dimOf c' → lbOf c' ≠ 0 → RowValid (basisOf c') (lbOf c')) →
    RowValid (basisOf c) (lbOf c)

theorem cover_direct : (List.range nCls).all (fun c => routeOf c != 0 || directL.contains c) = true := by
  decide +kernel
theorem cover_deg : (List.range nCls).all (fun c => routeOf c != 1 || degRows.any (fun d => d.1 == c)) = true := by
  decide +kernel
theorem cover_none : (List.range nCls).all (fun c => Nat.blt (routeOf c) 3 || lbOf c == 0) = true := by
  decide +kernel
theorem deg_dim : degRows.all (fun d => Nat.blt (dimOf d.1) (dimOf d.2.2.2.2.1) && Nat.blt d.2.2.2.2.1 nCls) = true := by
  decide +kernel
theorem dim_le : (List.range nCls).all (fun c => Nat.ble (dimOf c) 9) = true := by
  decide +kernel

/-- one class, given every strictly higher-dimensional class -/
theorem cls_step (hrun : RunHyp) (c : Nat) (hc : c < nCls) (hlb : lbOf c ≠ 0)
    (hhigh : ∀ c', c' < nCls → dimOf c < dimOf c' → lbOf c' ≠ 0 → RowValid (basisOf c') (lbOf c')) :
    RowValid (basisOf c) (lbOf c) := by
  have hmem : c ∈ List.range nCls := List.mem_range.mpr hc
  have hr3 : routeOf c < 3 := by
    have h := List.all_eq_true.mp cover_none c hmem
    simp only [Bool.or_eq_true, Nat.blt_eq, beq_iff_eq] at h
    rcases h with h | h
    · exact h
    · exact absurd h hlb
  rcases (by omega : routeOf c = 0 ∨ routeOf c = 1 ∨ routeOf c = 2) with h0 | h1 | h2
  · have h := List.all_eq_true.mp cover_direct c hmem
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
    rcases h with h | h
    · exact absurd h0 h
    · exact direct_ok c h
  · have h := List.all_eq_true.mp cover_deg c hmem
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨d, hd, hdc⟩
    · exact absurd h1 h
    · have hdd := List.all_eq_true.mp deg_dim d hd
      simp only [Bool.and_eq_true, Nat.blt_eq] at hdd
      obtain ⟨hdim, hjlt⟩ := hdd
      have hj : RowValid (basisOf d.2.2.2.2.1) (lbOf d.2.2.2.2.1) := by
        by_cases hj0 : lbOf d.2.2.2.2.1 = 0
        · rw [hj0]; exact rowValid_zero _
        · exact hhigh _ hjlt (by rw [← hdc]; exact hdim) hj0
      have := deg_rows_valid d hd hj
      rw [hdc] at this
      exact this
  · exact hrun c hc h2 hlb hhigh

/-- **hcls.** Every class the point IPs use is valid at the bound they use, given the E1 runs. -/
theorem hcls_all (hrun : RunHyp) : ∀ c, c < nCls → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c) := by
  have key : ∀ m, ∀ c, c < nCls → 10 - dimOf c = m → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc hm hlb
      apply cls_step hrun c hc hlb
      intro c' hc' hdim hlb'
      have h9 : dimOf c' ≤ 9 := by
        have h := List.all_eq_true.mp dim_le c' (List.mem_range.mpr hc')
        simpa using h
      exact ih (10 - dimOf c') (by omega) c' hc' rfl hlb'
  intro c hc hlb
  exact key _ c hc rfl hlb

end B334.Tab2
