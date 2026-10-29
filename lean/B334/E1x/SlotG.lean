import B334.E1x.CheckG
import B334.E1x.RT9

/-! # The slots of an E1G slot table from row-table entries (core Lean)

Moved out of `E1G/Check.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0), unchanged apart from the entry accessors
(`B334.E1x.RT`): a slot (264 bits) is `[127]` label mask, `[127]` reversed label mask, `[5]` cap. The label mask of an
entry's row is computed from the IP's label planes `LB` (plane `i` = bit `i` of every label representative, 128 bits
per plane): label `l` lies in the row iff every dual vector of the entry has even pairing with `vt l`. -/

namespace B334.E1x.SlotG
open B334.E1x.E1G

/-- labels whose representative has odd `<X, v>` (planes `LB`, 128 bits each) -/
def lpar (LB X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => cond (Nat.testBit X i) (Nat.xor acc (Nat.land (Nat.shiftRight LB (Nat.mul 128 i)) M127)) acc) 9
/-- label mask of an entry's row: the common kernel of its dual vectors -/
def labM (LB e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M127
    (fun j acc => Nat.land acc (Nat.xor M127 (lpar LB (RT.eV e (Nat.add (RT.eD e) j))))) (Nat.sub 9 (RT.eD e))
/-- the slot of entry `e` (label planes `LB`, reversed planes `LBR`) -/
def slot (LB LBR e : Nat) : Nat :=
  Nat.lor (labM LB e) (Nat.lor (Nat.shiftLeft (labM LBR e) 127) (Nat.shiftLeft (RT.eCap e) 254))
/-- every dual vector of `e` is a functional of the domain, i.e. `E ⊆ U` -/
def dualIn (DOM e : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j b => b && Nat.testBit DOM (RT.eV e (Nat.add (RT.eD e) j))) (Nat.sub 9 (RT.eD e))

end B334.E1x.SlotG
