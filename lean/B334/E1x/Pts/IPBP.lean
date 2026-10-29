import B334.E1x.P.Bridge3
import B334.E1x.IPChk

/-! # Boolean forms of the E1P `IPOK` structure fields (the E1P copy of `G/IPB.lean`)

The same conditions as `G/IPB.lean` at E1P's widths: 255 labels, label planes of 256 bits, 256-bit budget
fields (`E1P.fld`), 8-bit group fields (`E1PS.gpf`). `decide +kernel` on the bounded-quantifier statements runs out
of kernel memory; the `IPChk.allR` loops evaluate cheaply and the lemmas turn them back into the `Prop` fields of
`E1PS.IPOK`. -/

namespace B334.E1x.Pts
open B334.E1x.IPChk B334.E1x.E1PS

/-- `Cosets Em VT N` -/
def cosetsB (Em VT N : Nat) : Bool :=
  Em.testBit 0 &&
  allR (fun a => !Em.testBit a || allR (fun b => !Em.testBit b || Em.testBit (a ^^^ b)) 0 512) 0 512 &&
  allR (fun l => !Em.testBit (vt VT l)) 0 N &&
  allR (fun l => allR (fun l' => l == l' || !Em.testBit (vt VT l ^^^ vt VT l')) 0 N) 0 N &&
  allR (fun a => Em.testBit a || anyR (fun l => Em.testBit (a ^^^ vt VT l)) 0 N) 0 512

theorem cosets_of {Em VT N : Nat} (h : cosetsB Em VT N = true) : Cosets Em VT N := by
  unfold cosetsB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun a ha b hb hea heb => ?_, fun l hl => ?_, fun l hl l' hl' hne => ?_, fun a ha hea => ?_⟩
  · have e1 : (!Em.testBit a || allR (fun b => !Em.testBit b || Em.testBit (a ^^^ b)) 0 512) = true :=
      allR_spec0 h2 a ha
    rw [hea, Bool.not_true, Bool.false_or] at e1
    have e2 : (!Em.testBit b || Em.testBit (a ^^^ b)) = true := allR_spec0 e1 b hb
    rwa [heb, Bool.not_true, Bool.false_or] at e2
  · have e : (!Em.testBit (vt VT l)) = true := allR_spec0 h3 l hl
    rwa [Bool.not_eq_true'] at e
  · have e : (l == l' || !Em.testBit (vt VT l ^^^ vt VT l')) = true := allR_spec0 (allR_spec0 h4 l hl) l' hl'
    rw [Bool.or_eq_true] at e
    rcases e with e | e
    · exact absurd (beq_iff_eq.mp e) hne
    · rwa [Bool.not_eq_true'] at e
  · have e : (Em.testBit a || anyR (fun l => Em.testBit (a ^^^ vt VT l)) 0 N) = true := allR_spec0 h5 a ha
    rw [hea, Bool.false_or] at e
    obtain ⟨l, hl, hf⟩ := anyR_spec _ 0 N e
    rw [Nat.zero_add] at hf
    exact ⟨l, hl, hf⟩

/-- `DomPerp DOM Em` -/
def domperpB (DOM Em : Nat) : Bool :=
  allR (fun X => !DOM.testBit X || allR (fun a => !Em.testBit a || !B334.BC.par (a &&& X)) 0 512) 0 512

theorem domperp_of {DOM Em : Nat} (h : domperpB DOM Em = true) : DomPerp DOM Em := by
  unfold DomPerp
  intro X hX hd a ha he
  have e1 : (!DOM.testBit X || allR (fun a => !Em.testBit a || !B334.BC.par (a &&& X)) 0 512) = true :=
    allR_spec0 h X hX
  rw [hd, Bool.not_true, Bool.false_or] at e1
  have e2 : (!Em.testBit a || !B334.BC.par (a &&& X)) = true := allR_spec0 e1 a ha
  rwa [he, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at e2

/-- `Planes LB VT N` (planes of 256 bits) -/
def planesB (LB VT N : Nat) : Bool :=
  allR (fun i => allR (fun l => LB.testBit (256 * i + l) == (decide (l < N) && (vt VT l).testBit i)) 0 255) 0 9

theorem planes_of {LB VT N : Nat} (h : planesB LB VT N = true) : Planes LB VT N := by
  unfold Planes
  intro i hi l hl
  have e : (LB.testBit (256 * i + l) == (decide (l < N) && (vt VT l).testBit i)) = true :=
    allR_spec0 (allR_spec0 h i hi) l hl
  exact beq_iff_eq.mp e

/-- `PlanesR LB LBR` -/
def planesRB (LB LBR : Nat) : Bool :=
  allR (fun i => allR (fun j => LBR.testBit (256 * i + j) == LB.testBit (256 * i + (254 - j))) 0 255) 0 9

theorem planesR_of {LB LBR : Nat} (h : planesRB LB LBR = true) : PlanesR LB LBR := by
  unfold PlanesR
  intro i hi j hj
  have e : (LBR.testBit (256 * i + j) == LB.testBit (256 * i + (254 - j))) = true :=
    allR_spec0 (allR_spec0 h i hi) j hj
  exact beq_iff_eq.mp e

/-- the label-cap slots of `IPOK.capslot` -/
def capslotB (N nrows Ntab UB : Nat) (sl : Nat → Nat) : Bool :=
  allR (fun l => Nat.blt (nrows + l) Ntab &&
    allR (fun j => (smask (sl (nrows + l))).testBit j == decide (j = l)) 0 N &&
    scap (sl (nrows + l)) == E1P.fld UB l) 0 N

theorem capslot_of {N nrows Ntab UB : Nat} {sl : Nat → Nat} (h : capslotB N nrows Ntab UB sl = true) :
    ∀ l < N, nrows + l < Ntab ∧ (∀ j < N, (smask (sl (nrows + l))).testBit j = decide (j = l)) ∧
      scap (sl (nrows + l)) = E1P.fld UB l := by
  intro l hl
  have e : (Nat.blt (nrows + l) Ntab && allR (fun j => (smask (sl (nrows + l))).testBit j == decide (j = l)) 0 N &&
      scap (sl (nrows + l)) == E1P.fld UB l) = true := allR_spec0 h l hl
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨e1, e2⟩, e3⟩ := e
  rw [Nat.blt_eq] at e1
  exact ⟨e1, fun j hj => beq_iff_eq.mp (allR_spec0 e2 j hj), beq_iff_eq.mp e3⟩

/-- `IPOK.UB_le` -/
def ubleB (UB : Nat) : Bool := allR (fun l => Nat.ble (E1P.fld UB l) (2 ^ 32)) 0 255

theorem uble_of {UB : Nat} (h : ubleB UB = true) : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32 := by
  intro l hl
  have e : Nat.ble (E1P.fld UB l) (2 ^ 32) = true := allR_spec0 h l hl
  rwa [Nat.ble_eq] at e

/-- `GElt Em VT N gp P Q` -/
def geltB (Em VT N gp P Q : Nat) : Bool :=
  isGL P && isGL Q && allR (fun a => Em.testBit (actF P Q a) == Em.testBit a) 0 512 &&
    allR (fun l => Nat.blt (gpf gp l) N && Em.testBit (actF P Q (vt VT l) ^^^ vt VT (gpf gp l))) 0 N

theorem gelt_of {Em VT N gp P Q : Nat} (h : geltB Em VT N gp P Q = true) : GElt Em VT N gp P Q := by
  unfold geltB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun a ha => beq_iff_eq.mp (allR_spec0 h3 a ha), fun l hl => ?_⟩
  have e : (Nat.blt (gpf gp l) N && Em.testBit (actF P Q (vt VT l) ^^^ vt VT (gpf gp l))) = true :=
    allR_spec0 h4 l hl
  rw [Bool.and_eq_true, Nat.blt_eq] at e
  exact e

end B334.E1x.Pts
