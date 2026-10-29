import B334.Tab2.Induct

/-! # From the per-run theorems to `RunHyp` (the dispatcher)

Each E1 production run proves `run_c : HighHyp c → RowValid (basisOf c) (lbOf c)` for its class `c`: the class is
valid once every strictly higher-dimensional class is (an IP's rows are strict superspaces of its E). A generated
module collects them for a list `L` of classes (`runs_cons` / `runs_append` build the hypothesis `hL` in balanced
chunks), and `runHyp_of_list` turns `hL` plus a kernel check that `L` contains every class with `routeOf c = 2` and
`lbOf c ≠ 0` into `RunHyp`. -/

namespace B334.Tab2

open B334

/-- every strictly higher-dimensional class is valid (the hypothesis of a run theorem) -/
def HighHyp (c : Nat) : Prop :=
  ∀ c', c' < nCls → dimOf c < dimOf c' → lbOf c' ≠ 0 → RowValid (basisOf c') (lbOf c')

/-- the run theorems for the classes of `L` -/
def RunsFor (L : List Nat) : Prop := ∀ c ∈ L, HighHyp c → RowValid (basisOf c) (lbOf c)

theorem runs_nil : RunsFor [] := fun _ h => nomatch h

theorem runs_cons {c : Nat} {L : List Nat} (h : HighHyp c → RowValid (basisOf c) (lbOf c)) (hL : RunsFor L) :
    RunsFor (c :: L) := by
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | h'
  · exact h
  · exact hL c' h'

theorem runs_append {L₁ L₂ : List Nat} (h₁ : RunsFor L₁) (h₂ : RunsFor L₂) : RunsFor (L₁ ++ L₂) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

/-- **The dispatcher.** -/
theorem runHyp_of_list (L : List Nat) (hL : RunsFor L)
    (hcov : (List.range nCls).all (fun c => routeOf c != 2 || lbOf c == 0 || L.contains c) = true) : RunHyp := by
  intro c hc hr hlb hhigh
  have h := List.all_eq_true.mp hcov c (List.mem_range.mpr hc)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · exact absurd hr h
  · exact absurd h hlb
  · exact hL c h hhigh

end B334.Tab2
