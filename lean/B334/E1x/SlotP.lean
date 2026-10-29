import B334.E1x.CheckP
import B334.E1x.RT9

/-! # The slots of an E1P slot table from row-table entries (core Lean)

Moved out of `E1P/Check.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0), unchanged apart from the entry accessors
(`B334.E1x.RT`): a slot (520 bits) is `[255]` label mask, `[255]` reversed label mask, `[5]` cap; the label planes `LB`
have 256 bits per plane. -/

namespace B334.E1x.SlotP
open B334.E1x.E1P

/-- labels whose representative has odd `<X, v>` (planes `LB`, 256 bits each) -/
def lpar (LB X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => cond (Nat.testBit X i) (Nat.xor acc (Nat.land (Nat.shiftRight LB (Nat.mul 256 i)) M255)) acc) 9
/-- label mask of an entry's row: the common kernel of its dual vectors -/
def labM (LB e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M255
    (fun j acc => Nat.land acc (Nat.xor M255 (lpar LB (RT.eV e (Nat.add (RT.eD e) j))))) (Nat.sub 9 (RT.eD e))
/-- the slot of entry `e` (label planes `LB`, reversed planes `LBR`) -/
def slot (LB LBR e : Nat) : Nat :=
  Nat.lor (labM LB e) (Nat.lor (Nat.shiftLeft (labM LBR e) 255) (Nat.shiftLeft (RT.eCap e) 510))
/-- every dual vector of `e` is a functional of the domain, i.e. `E ⊆ U` -/
def dualIn (DOM e : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j b => b && Nat.testBit DOM (RT.eV e (Nat.add (RT.eD e) j))) (Nat.sub 9 (RT.eD e))

end B334.E1x.SlotP
