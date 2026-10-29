import B334.Tables.SymTab

/-! # Range parts of the `allLT 4096` table facts (memory split of `SymTabWC_<o>` and `SymTabOrb`)

A kernel fact `allLT 4096 f = true` is checked in `P` parts of `C` masks each (`C * P = 4096`), one module per part,
so that no module holds the kernel's evaluation of all 4096 entries (the unsplit facts took 11.7–13.0 GB).
* `allFrom lo n f`: `f` holds on `lo, …, lo + n - 1` (the same recursor loop as `allLT`, shifted).
* `allLT_add`: `allLT (a + b) f = (allLT a f && allFrom a b f)`; `allLT_of_parts`: the parts give the whole fact.
* `wcAt o W C`: the entry check of `wcOK` (`wcOK_eq` is `rfl`), so the parts of `wc_fact_o` can name it.
The part modules `Split/WC_<o>_<j>`, `Split/WB_<j>` and the combining modules `SymTabWC_<o>`, `SymTabOrb` are generated
by a script. -/

namespace B334.Tab
open B334.Core

/-- `f i` for all `lo ≤ i < lo + n` -/
def allFrom (lo n : Nat) (f : Nat → Bool) : Bool := allLT n (fun k => f (lo + k))

theorem allLT_add (a b : Nat) (f : Nat → Bool) : allLT (a + b) f = (allLT a f && allFrom a b f) := by
  induction b with
  | zero =>
    show allLT a f = (allLT a f && true)
    rw [Bool.and_true]
  | succ b ih =>
    show (f (a + b) && allLT (a + b) f) = (allLT a f && (f (a + b) && allFrom a b f))
    rw [ih]
    cases f (a + b) <;> cases allLT a f <;> cases allFrom a b f <;> rfl

/-- **the combining lemma**: `P` parts of `C` masks give `allLT (C * P)` -/
theorem allLT_of_parts (C : Nat) (f : Nat → Bool) :
    ∀ P : Nat, (∀ j < P, allFrom (C * j) C f = true) → allLT (C * P) f = true
  | 0, _ => rfl
  | P + 1, h => by
    have h1 := allLT_of_parts C f P (fun j hj => h j (by omega))
    have h2 := h P (by omega)
    simp only [Nat.mul_succ, allLT_add, h1, h2, Bool.and_self]

/-- the entry check of `wcOK` -/
def wcAt (o W C c : Nat) : Bool := c == 0 ||
  (mul44 (pS W c) (pSi W c) == 33825 && mulBS o (pS W c) == o && C.testBit (mulSC (pSi W c) c))

theorem wcOK_eq (o W C : Nat) : wcOK o W C = allLT 4096 (wcAt o W C) := rfl

end B334.Tab
