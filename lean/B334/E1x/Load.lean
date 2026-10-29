import Lean

/-! # Loading big literals from binary files (no numeral elaboration)

Ported from the ⟨3,3,3⟩ release (`RT/Load.lean`, `E1/E1Load.lean`, Apache-2.0) to this tree (plain `import`, no module
headers). A hex numeral of a million bits takes about half a minute to elaborate; these commands read a binary file at
elaboration time and add the constants with `mkRawNatLit`, so the kernel sees the same literals at no parsing cost.
Every definition is still checked by the kernel as usual, and nothing here is trusted: a wrong file only makes the
later kernel checks fail. Paths are relative to the directory `lean` runs in (the build's `lean/` directory).

* `#e1lits Pfx "file"`: the file holds `u32 count`, then per literal `u32 nbytes` and its little-endian bytes. Defines
  `Pfx.L<i>` (raw literals), `Pfx.lits : List Nat` (in file order) and `Pfx.n`.
* `#rttablew Pfx "file" ch w`: entries of `w` bits (`w / 8` bytes each, little-endian) in `file`; defines `Pfx.C<k>`
  (chunk `k`: `ch` entries as one raw literal), the dispatcher `Pfx.D<l>_<i>` (one `Bool.rec` per bit of the chunk
  index), `Pfx.chunk`, `Pfx.entry i` and `Pfx.N`. -/

open Lean Elab Command

namespace B334.E1x.Load

/-- little-endian bytes `[lo, hi)` of `b` as a Nat, divide and conquer -/
partial def natLE (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi - lo ≤ 64 then Id.run do
    let mut acc := 0
    let mut i := hi
    while i > lo do
      i := i - 1
      acc := acc * 256 + (b.get! i).toNat
    return acc
  else
    let mid := lo + (hi - lo) / 2
    natLE b lo mid + (natLE b mid hi <<< (8 * (mid - lo)))

def natTy : Expr := mkConst ``Nat

def defN (n : Name) (ty v : Expr) : CoreM Unit := do
  let dv : DefinitionVal := { name := n, levelParams := [], type := ty, value := v,
                              hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)

/-- `Nat.beq (Nat.land (Nat.shiftRight k b) 1) 1` -/
def bitE (k : Expr) (b : Nat) : Expr :=
  mkApp2 (mkConst ``Nat.beq)
    (mkApp2 (mkConst ``Nat.land) (mkApp2 (mkConst ``Nat.shiftRight) k (mkRawNatLit b)) (mkRawNatLit 1)) (mkRawNatLit 1)

def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat + 65536 * (b.get! (i + 2)).toNat + 16777216 * (b.get! (i + 3)).toNat

def e1lits (pfx : Name) (path : String) : CommandElabM Unit := do
  let b ← IO.FS.readBinFile path
  if b.size < 4 then throwError "#e1lits: {path}: too short"
  let cnt := u32 b 0
  let mut off := 4
  let mut names : Array Name := #[]
  for i in [0:cnt] do
    if b.size < off + 4 then throwError "#e1lits: {path}: truncated at literal {i}"
    let nb := u32 b off
    off := off + 4
    if b.size < off + nb then throwError "#e1lits: {path}: truncated in literal {i}"
    let v := natLE b off (off + nb)
    off := off + nb
    let nm := pfx ++ Name.mkSimple s!"L{i}"
    liftCoreM <| defN nm natTy (mkRawNatLit v)
    names := names.push nm
  if off != b.size then throwError "#e1lits: {path}: {b.size - off} trailing bytes"
  let listTy := mkApp (mkConst ``List [Level.zero]) natTy
  let mut lst : Expr := mkApp (mkConst ``List.nil [Level.zero]) natTy
  for nm in names.reverse do
    lst := mkApp3 (mkConst ``List.cons [Level.zero]) natTy (mkConst nm) lst
  liftCoreM <| defN (pfx ++ `lits) listTy lst
  liftCoreM <| defN (pfx ++ `n) natTy (mkRawNatLit cnt)
  logInfo m!"#e1lits {pfx}: {cnt} literals, {b.size} bytes"

elab "#e1lits " pfx:ident p:str : command => e1lits pfx.getId p.getString

def rttable (pfx : Name) (path : String) (ch : Nat) (wb : Nat) : CommandElabM Unit := do
  let b ← IO.FS.readBinFile path
  if wb % 8 != 0 || wb == 0 || ch == 0 then throwError "#rttablew: width must be a positive multiple of 8, ch > 0"
  let wB := wb / 8
  if b.size % wB != 0 then throwError "#rttablew: {path}: size {b.size} is not a multiple of {wB}"
  let n := b.size / wB
  let nch := (n + ch - 1) / ch
  let pf := pfx
  for k in [0:nch] do
    liftCoreM <| defN (pf ++ Name.mkSimple s!"C{k}") natTy
      (mkRawNatLit (natLE b (wB * ch * k) (min b.size (wB * ch * (k + 1)))))
  let dep := Nat.max 1 (Nat.log2 (nch - 1) + 1)
  let fnTy := mkForall `k BinderInfo.default natTy natTy
  for lvl in [1:dep + 1] do
    let cnt := (nch + 2 ^ lvl - 1) / 2 ^ lvl
    for idx in [0:cnt] do
      let kv := mkBVar 0
      let child (c : Nat) : Expr :=
        if lvl == 1 then (if c < nch then mkConst (pf ++ Name.mkSimple s!"C{c}") else mkRawNatLit 0)
        else (if c * 2 ^ (lvl - 1) < nch then mkApp (mkConst (pf ++ Name.mkSimple s!"D{lvl-1}_{c}")) kv
              else mkRawNatLit 0)
      let body := mkApp4 (mkConst ``Bool.rec [Level.one]) (mkLambda `_ BinderInfo.default (mkConst ``Bool) natTy)
        (child (2 * idx)) (child (2 * idx + 1)) (bitE kv (lvl - 1))
      liftCoreM <| defN (pf ++ Name.mkSimple s!"D{lvl}_{idx}") fnTy (mkLambda `k BinderInfo.default natTy body)
  liftCoreM <| defN (pf ++ `chunk) fnTy
    (mkLambda `k BinderInfo.default natTy (mkApp (mkConst (pf ++ Name.mkSimple s!"D{dep}_0")) (mkBVar 0)))
  -- entry i = (chunk (i / ch) >>> (wb * (i % ch))) &&& (2^wb - 1)
  let iv := mkBVar 0
  let ent := mkApp2 (mkConst ``Nat.land)
    (mkApp2 (mkConst ``Nat.shiftRight) (mkApp (mkConst (pf ++ `chunk)) (mkApp2 (mkConst ``Nat.div) iv (mkRawNatLit ch)))
      (mkApp2 (mkConst ``Nat.mul) (mkRawNatLit wb) (mkApp2 (mkConst ``Nat.mod) iv (mkRawNatLit ch))))
    (mkRawNatLit (2 ^ wb - 1))
  liftCoreM <| defN (pf ++ `entry) fnTy (mkLambda `i BinderInfo.default natTy ent)
  liftCoreM <| defN (pf ++ `N) natTy (mkRawNatLit n)
  logInfo m!"#rttablew {pf}: {n} entries of {wb} bits, {nch} chunks, depth {dep}"

elab "#rttablew " pfx:ident p:str ch:num w:num : command => rttable pfx.getId p.getString ch.getNat w.getNat

end B334.E1x.Load
