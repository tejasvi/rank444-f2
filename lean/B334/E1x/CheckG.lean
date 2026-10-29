import B334.E1x.TabG

/-! # E1G for ⟨3,3,4⟩: the enumeration checker for coset IPs with up to 127 labels (core Lean only)

Port of `E1G/Check.lean` from the ⟨3,3,3⟩ release (`rank333-f2`, Apache-2.0).
The checker is the 333 one with these changes:
- delegated records hold up to **25** prefix labels and **4-bit** budgets: `[5] d, [7] pos, d × [7] prefix, 127 × [4]
  budgets`, zero-padded to **695** bits (333: 21 labels, 3-bit budgets, 540 bits); mode-1 headers carry `127 × [4]`
  budgets; budget fixings carry a `[4] ν`;
- dual supports have an **8-bit** count `k` (333: 6 bits; the traces have k up to 83);
- the node fuel is **32** levels (333: 24), enough for a block rooted at depth 0 with R ≤ 31;
- the leaf test is a parameter `Ctx.LF` on the packed leaf prefix `pl` (`R` labels, `[7]` each): a leaf node
  carries no certificate and is accepted iff `C.LF pl = true`. At assembly `LF` is membership in the run's leaf list,
  and the soundness proof takes, for every listed prefix, a BranchCheck334 certificate accepted on the leaf record
  `leafRec C.R C.VT C.DOM pl cert` (v7 layout = v5c-334 layout: `[6] n`, n × 9-bit first factors, dom mode
  `01`, 512-bit domain, certificate), so the E1 replay never evaluates a certificate. 333's external leaves
  (`Ctx.EXT`) and its inline `BC7.leafS` call are dropped;
- the slot construction from row-table entries (333 `lpar`, `labM`, `slot`, `dualIn`) moves to the binding layer, so this
  module imports no Mathlib.

Labels have 7 bits and `N ≤ 127`. Packed vectors have 128 fields of 128 bits (`ECT`). Slots have 264 bits: `[127]` label
mask, `[127]` reversed mask, `[5]` cap. Slot-table indices have 15 bits. Group permutations have 7-bit fields (896 bits
per element); witnesses are `[11]` indices of the group function `C.GP`.

**Block.**
- Header: `[1] mode`, `[5] d`, `[7] pos`, `d × [7]` prefix labels (ascending); mode 1 adds `127 × [4]` budgets.
- `[8] nd`, then `nd × [695]` delegated child states, each `[5] d, [7] pos, d × [7] prefix, 127 × [4] budgets`,
  zero-padded, so `d ≤ 25`.
- `[12] k`, then `k × [15]` slot-table indices: the block's row table.
- Mode 0 only: `[8] n`, then `n × [12]` rows saturated at the start.
- Then the node.

**Node.** A `[2]` tag, then:
- 0, leaf: nothing more (the prefix must have `R` labels and pass `C.LF`).
- 1, kill: `[8] k, k × ([12] row, [36] Y)`.
- 2, branch: `[7] cut, [2] kind, (kind 1: [12] row), [1] hd, (hd: [8] k, k × ([12], [36]), [7] nfix, nfix × ([7] l,
  [4] ν))`.

A branch then has, per label in `[pos, min(cut, N))`, a `[2]` code: 0 skip; 3 non-canonical `[11] g`; 1 lookahead-killed
child `[6] n, n × [12], [1] pk, (pk 1: [12] row)`; 2 child subtree `[6] n, n × [12], [24] len, node` (`len = 0`:
delegated, then `[8]` the index of its state in the block header). -/

namespace B334.E1x.E1G
open B334.E1x.ECT

local macro "sel " c:term:max a:term:max b:term:max : term => `(@Bool.rec (fun _ => _) $b $a $c)
local macro:35 a:term:36 " ∧ᵇ " b:term:35 : term => `(@Bool.rec (fun _ => Bool) false $b $a)

noncomputable section

@[inline] def rd (k S : Nat) : Nat := Nat.land S (Nat.sub (Nat.shiftLeft 1 k) 1)
@[inline] def sk (k S : Nat) : Nat := Nat.shiftRight S k
@[inline] def FM : Nat := 0xffffffffffffffffffffffffffffffff
@[inline] def M64 : Nat := 0xffffffffffffffff
@[inline] def M127 : Nat := 0x7fffffffffffffffffffffffffffffff
@[inline] def SC : Nat := 1073741824
@[inline] def spread (m : Nat) : Nat := Nat.land (Nat.mul m SPM) REP
@[inline] def fmask (m : Nat) : Nat := Nat.mul (spread m) FM
/-- the sum of the fields: `v mod (2^128 - 1)` (exact while the sum is below `2^128 - 1`) -/
@[inline] def fsum (v : Nat) : Nat := Nat.mod v FM
@[inline] def dot (vr x : Nat) : Nat := Nat.land (Nat.shiftRight (Nat.mul vr x) 16128) FM
@[inline] def fld (v l : Nat) : Nat := Nat.land (Nat.shiftRight v (Nat.mul 128 l)) FM
@[inline] def hif (lo : Nat) : Nat := Nat.shiftLeft (Nat.shiftRight FMALL (Nat.mul 128 lo)) (Nat.mul 128 lo)
@[inline] def one (l : Nat) : Nat := Nat.shiftLeft 1 (Nat.mul 128 l)
@[inline] def oner (l : Nat) : Nat := Nat.shiftLeft 1 (Nat.mul 128 (Nat.sub 126 l))
@[inline] def deficit (T UFR lo : Nat) : Nat :=
  let D := Nat.sub DSCREP T
  dot UFR (Nat.land (Nat.land D (Nat.mul (Nat.land (Nat.shiftRight D 64) REP) M64)) (hif lo))

@[inline] def MSL : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
/-- slot `j` of the row table (the three accessors share it through the kernel's cache) -/
@[inline] def slotAt (RTb j : Nat) : Nat := Nat.land (Nat.shiftRight RTb (Nat.mul 264 j)) MSL
@[inline] def rmask (RTb j : Nat) : Nat := Nat.land (slotAt RTb j) M127
@[inline] def rmaskr (RTb j : Nat) : Nat := Nat.land (Nat.shiftRight (slotAt RTb j) 127) M127
@[inline] def rcap (RTb j : Nat) : Nat := Nat.land (Nat.shiftRight (slotAt RTb j) 254) 31
/-- weight of the budgets at labels `≥ lo` outside the label mask `m` -/
@[inline] def wout (UF m lo : Nat) : Nat := fsum (Nat.land (Nat.land UF (Nat.xor FMALL (fmask m))) (hif lo))

/-! ## The per-operation definitions as macros (each macro is its definition's body; `rfl` relates the two forms) -/
local macro "rd " k:term:max S:term:max : term => `(Nat.land $S (Nat.sub (Nat.shiftLeft 1 $k) 1))
local macro "sk " k:term:max S:term:max : term => `(Nat.shiftRight $S $k)
local macro "spread " m:term:max : term => `(Nat.land (Nat.mul $m SPM) REP)
local macro "fmask " m:term:max : term => `(Nat.mul (spread $m) FM)
local macro "fsum " v:term:max : term => `(Nat.mod $v FM)
local macro "dot " vr:term:max x:term:max : term => `(Nat.land (Nat.shiftRight (Nat.mul $vr $x) 16128) FM)
local macro "fld " v:term:max l:term:max : term => `(Nat.land (Nat.shiftRight $v (Nat.mul 128 $l)) FM)
local macro "hif " lo:term:max : term => `(Nat.shiftLeft (Nat.shiftRight FMALL (Nat.mul 128 $lo)) (Nat.mul 128 $lo))
local macro "one " l:term:max : term => `(Nat.shiftLeft 1 (Nat.mul 128 $l))
local macro "oner " l:term:max : term => `(Nat.shiftLeft 1 (Nat.mul 128 (Nat.sub 126 $l)))
local macro "deficit " T:term:max UFR:term:max lo:term:max : term =>
  `(dot $UFR (Nat.land (Nat.land (Nat.sub DSCREP $T) (Nat.mul (Nat.land (Nat.shiftRight (Nat.sub DSCREP $T) 64) REP) M64)) (hif $lo)))
local macro "slotAt " RTb:term:max j:term:max : term => `(Nat.land (Nat.shiftRight $RTb (Nat.mul 264 $j)) MSL)
local macro "rmask " RTb:term:max j:term:max : term => `(Nat.land (slotAt $RTb $j) M127)
local macro "rmaskr " RTb:term:max j:term:max : term => `(Nat.land (Nat.shiftRight (slotAt $RTb $j) 127) M127)
local macro "rcap " RTb:term:max j:term:max : term => `(Nat.land (Nat.shiftRight (slotAt $RTb $j) 254) 31)
local macro "wout " UF:term:max m:term:max lo:term:max : term => `(fsum (Nat.land (Nat.land $UF (Nat.xor FMALL (fmask $m))) (hif $lo)))

/-! ## The block's row table -/

/-- the row table of the `n` slots indexed by `IX` (`n × [15]`), divide and conquer (`h` levels of fuel; out of fuel, a
remaining range of more than one slot gives no slots, which is sound) -/
def mkRTd (sl : Nat → Nat) (h : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun n IX => sel (Nat.beq n 1) (sl (rd 15 IX)) 0)
    (fun _ ih n IX => sel (Nat.ble n 1) (sel (Nat.beq n 1) (sl (rd 15 IX)) 0)
      (Nat.lor (ih (Nat.shiftRight n 1) (rd (Nat.mul 15 (Nat.shiftRight n 1)) IX))
        (Nat.shiftLeft (ih (Nat.sub n (Nat.shiftRight n 1)) (sk (Nat.mul 15 (Nat.shiftRight n 1)) IX))
          (Nat.mul 264 (Nat.shiftRight n 1))))) h
/-- the block's row table from `k` slot indices (`[15]` each) and the rest of the stream -/
def mkRT (sl : Nat → Nat) (k S : Nat) : Nat × Nat := (mkRTd sl 13 k (rd (Nat.mul 15 k) S), sk (Nat.mul 15 k) S)

/-! ## Slot tables in chunks (as 333: `sl := slc P.chunk` caches one dispatch per chunk of 64 slots) -/

/-- chunk `c`, cached by the kernel per chunk -/
def chunkL (ch : Nat → Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.add (ch 0) 0) (fun n _ => Nat.add (ch (Nat.succ n)) 0) c
/-- slot `i` of a slot table in chunks of 64 slots of 264 bits -/
def slc (ch : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (chunkL ch (Nat.shiftRight i 6)) (Nat.mul 264 (Nat.land i 63))) MSL

/-- read a dual of `k` rows (`[12]` slot, `[36] Y`): `(∑ Y cap, T, rest)` -/
def rdual (RTb k S : Nat) : Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat × Nat) (fun BC T S => (BC, T, S))
    (fun _ ih BC T S => ih (Nat.add BC (Nat.mul (rd 36 (sk 12 S)) (rcap RTb (rd 12 S))))
      (Nat.add T (Nat.mul (rd 36 (sk 12 S)) (spread (rmask RTb (rd 12 S))))) (sk 48 S)) k 0 0 S

/-- saturation events: `n` slots; each row must be full (`m(U) = cap` for the multiplicity vector `MV`).  Returns
`(ok, ∪ masks, ∪ reversed masks, rest)` -/
def satsM (RTb n MV S : Nat) : Bool × Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Bool → Nat → Nat → Nat → Bool × Nat × Nat × Nat) (fun ok M MR S => (ok, M, MR, S))
    (fun _ ih ok M MR S =>
      ih (ok ∧ᵇ Nat.beq (fsum (Nat.land MV (fmask (rmask RTb (rd 12 S))))) (rcap RTb (rd 12 S)))
        (Nat.lor M (rmask RTb (rd 12 S))) (Nat.lor MR (rmaskr RTb (rd 12 S))) (sk 12 S)) n true 0 0 S

/-- the budgets after a saturation result `r`: those of the union of the full rows are zeroed -/
def satsZ (UF UFR : Nat) (r : Bool × Nat × Nat × Nat) : Bool × Nat × Nat × Nat :=
  (r.1, Nat.land UF (Nat.xor FMALL (fmask r.2.1)), Nat.land UFR (Nat.xor FMALL (fmask r.2.2.1)), r.2.2.2)

/-- saturation events for the multiplicity vector `MV` on the budgets `UF`, `UFR` -/
def sats (RTb n MV UF UFR S : Nat) : Bool × Nat × Nat × Nat := satsZ UF UFR (satsM RTb n MV S)

/-- budget fixings `(l, ν)` (`[7] l, [4] ν`) from a node dual: `(ν + 1)(T_l - SC) > gap` and `ν < u_l` -/
def fixes (n T gap UF UFR S : Nat) : Bool × Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Bool → Nat → Nat → Nat → Bool × Nat × Nat × Nat) (fun ok UF UFR S => (ok, UF, UFR, S))
    (fun _ ih ok UF UFR S =>
      let l := rd 7 S
      let nu := rd 4 (sk 7 S)
      let u := fld UF l
      let t := fld T l
      ih (ok ∧ᵇ Nat.ble (Nat.succ SC) t ∧ᵇ Nat.ble (Nat.succ nu) u ∧ᵇ Nat.ble (Nat.succ gap) (Nat.mul (Nat.succ nu) (Nat.sub t SC)))
        (Nat.sub UF (Nat.mul (Nat.sub u nu) (one l))) (Nat.sub UFR (Nat.mul (Nat.sub u nu) (oner l))) (sk 11 S)) n true UF UFR S

/-! ## Canonicity witnesses -/

/-- the reversed packing of the image of the multiset with labels `pl` (`m` entries, `[7]` each) under the label
permutation `gp` (7-bit fields) -/
def imgR (gp pl m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
    (fun _ ih acc pl => ih (Nat.add acc (oner (Nat.land (Nat.shiftRight gp (Nat.mul 7 (rd 7 pl))) 127))) (sk 7 pl)) m 0 pl

/-! ## Leaves -/

/-- the leaf record of the prefix `pl` (`R` labels) with certificate `cert`: `[6] R`, terms (9-bit first factors
`VT[label]`), dom mode `01`, `DOM`, cert (v7 = v5c-334 layout). Not called by the checker: the soundness proof applies
BranchCheck334's leaf theorem to it -/
def leafRec (R VT DOM pl cert : Nat) : Nat :=
  let terms := Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc i pl => ih (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight VT (Nat.mul 9 (rd 7 pl))) 511) (Nat.mul 9 i)))
      (Nat.succ i) (sk 7 pl)) R 0 0 pl
  Nat.lor R (Nat.lor (Nat.shiftLeft terms 6) (Nat.shiftLeft (Nat.lor 1 (Nat.lor (Nat.shiftLeft DOM 2) (Nat.shiftLeft cert 514)))
    (Nat.add 6 (Nat.mul 9 R))))

/-! ## States -/

/-- packed budgets (field `l` at `128 l`) from `127 × [4]` fields -/
def budU (B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l U => Nat.add U (Nat.mul (rd 4 (sk (Nat.mul 4 l) B)) (one l))) 127
/-- reversed packed budgets (field `l` at `128 (126 - l)`) -/
def budUR (B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l U => Nat.add U (Nat.mul (rd 4 (sk (Nat.mul 4 l) B)) (oner l))) 127
/-- the record `r` (`[5] d, [7] pos, d × [7] prefix, 127 × [4] budgets`) is the state `(d, pos, pl, UF)` -/
def stEq (r d pos pl UF : Nat) : Bool :=
  Nat.beq (rd 5 r) d ∧ᵇ Nat.beq (rd 7 (sk 5 r)) pos ∧ᵇ Nat.beq (rd (Nat.mul 7 d) (sk 12 r)) pl ∧ᵇ
    Nat.beq (budU (sk (Nat.add 12 (Nat.mul 7 d)) r)) UF

structure Ctx where
  R : Nat
  N : Nat
  VT : Nat
  DOM : Nat
  GP : Nat → Nat
  /-- the leaf test on the packed prefix (membership in the run's leaf list, at assembly) -/
  LF : Nat → Bool

/-- a leaf of prefix `pl` -/
def leafOK (C : Ctx) (pl : Nat) : Bool := C.LF pl

/-! ## The node -/

/-- a child with codes 1 (lookahead-killed) or 2 (subtree), after its saturation events `s` -/
def kidC12 (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (C : Ctx) (RTb H : Nat)
    (code d pl MV MVR l : Nat) (ihl : Nat → Nat → Bool) (s : Bool × Nat × Nat × Nat) : Bool :=
  sel (Nat.beq code 1)
    (sel (Nat.beq (rd 1 s.2.2.2) 0)
      (Nat.blt (wout s.2.1 0 l) (Nat.sub C.R (Nat.succ d)) ∧ᵇ ihl (Nat.succ l) (sk 1 s.2.2.2))
      (Nat.ble 1 (Nat.sub (Nat.add (Nat.sub C.R (Nat.succ d)) (fsum (Nat.land (Nat.add MV (one l))
          (fmask (rmask RTb (rd 12 (sk 1 s.2.2.2))))))) (rcap RTb (rd 12 (sk 1 s.2.2.2)))) ∧ᵇ
       Nat.blt (wout s.2.1 (rmask RTb (rd 12 (sk 1 s.2.2.2))) l)
         (Nat.sub (Nat.add (Nat.sub C.R (Nat.succ d)) (fsum (Nat.land (Nat.add MV (one l))
          (fmask (rmask RTb (rd 12 (sk 1 s.2.2.2))))))) (rcap RTb (rd 12 (sk 1 s.2.2.2)))) ∧ᵇ
       ihl (Nat.succ l) (sk 13 s.2.2.2)))
    (sel (Nat.beq (rd 24 s.2.2.2) 0)
      (stEq (rd 695 (sk (Nat.mul 695 (rd 8 (sk 24 s.2.2.2))) H)) (Nat.succ d) l
          (Nat.lor pl (Nat.shiftLeft l (Nat.mul 7 d))) s.2.1 ∧ᵇ ihl (Nat.succ l) (sk 32 s.2.2.2))
      (ih (Nat.succ d) l (Nat.lor pl (Nat.shiftLeft l (Nat.mul 7 d))) (Nat.add MV (one l)) (Nat.add MVR (oner l))
          s.2.1 s.2.2.1 (rd (rd 24 s.2.2.2) (sk 24 s.2.2.2)) ∧ᵇ
        ihl (Nat.succ l) (sk (Nat.add 24 (rd 24 s.2.2.2)) s.2.2.2)))

/-- one label of the children loop (`ihl`: the rest of the loop) -/
def kidStep (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (C : Ctx) (RTb H : Nat)
    (d pl MV MVR UF UFR : Nat) (ihl : Nat → Nat → Bool) (l S : Nat) : Bool :=
  sel (Nat.beq (rd 2 S) 0)
    (Nat.beq (fld UF l) 0 ∧ᵇ ihl (Nat.succ l) (sk 2 S))
    (sel (Nat.beq (rd 2 S) 3)
      (Nat.blt (Nat.add MVR (oner l))
          (imgR (C.GP (rd 11 (sk 2 S))) (Nat.lor pl (Nat.shiftLeft l (Nat.mul 7 d))) (Nat.succ d)) ∧ᵇ
        ihl (Nat.succ l) (sk 11 (sk 2 S)))
      (Nat.ble 1 (fld UF l) ∧ᵇ
        (sats RTb (rd 6 (sk 2 S)) (Nat.add MV (one l)) (Nat.sub UF (one l)) (Nat.sub UFR (oner l)) (sk 6 (sk 2 S))).1 ∧ᵇ
        kidC12 ih C RTb H (rd 2 S) d pl MV MVR l ihl
          (sats RTb (rd 6 (sk 2 S)) (Nat.add MV (one l)) (Nat.sub UF (one l)) (Nat.sub UFR (oner l)) (sk 6 (sk 2 S)))))

/-- the children loop of a branch node over `cnt` labels from `l` -/
def kids (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (C : Ctx) (RTb H : Nat)
    (cnt d pl MV MVR UF UFR l S : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ihl l S => kidStep ih C RTb H d pl MV MVR UF UFR ihl l S) cnt l S

/-- the cut condition: no completion has all its new labels `≥ cut` -/
def cutOK (C : Ctx) (RTb kind cut cj rem MV UF' : Nat) (hd : Bool) (BC T UFR' RS : Nat) : Bool :=
  sel (Nat.beq kind 0) (Nat.ble C.N cut)
    (sel (Nat.beq kind 1)
      (Nat.ble 1 (Nat.sub (Nat.add rem (fsum (Nat.land MV (fmask (rmask RTb cj))))) (rcap RTb cj)) ∧ᵇ
       Nat.blt (wout UF' (rmask RTb cj) cut) (Nat.sub (Nat.add rem (fsum (Nat.land MV (fmask (rmask RTb cj))))) (rcap RTb cj)))
      (sel (Nat.beq kind 2) (Nat.blt (wout UF' 0 cut) rem)
        (hd ∧ᵇ Nat.blt (Nat.add BC (deficit T UFR' cut)) RS)))

/-- a branch node after its dual `du` (`(∑ Y cap, T, rest)`) and budget fixings `fx` -/
def branchT (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (C : Ctx) (RTb H : Nat)
    (d pos pl MV MVR UFR rem cut kind cj : Nat) (hd : Bool) (du : Nat × Nat × Nat) (fx : Bool × Nat × Nat × Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) true
    (Nat.ble (Nat.add (Nat.mul rem SC) (dot MVR du.2.1)) (Nat.add du.1 (deficit du.2.1 UFR pos))) hd) ∧ᵇ fx.1 ∧ᵇ
    cutOK C RTb kind cut cj rem MV fx.2.1 hd du.1 du.2.1 fx.2.2.1 (Nat.add (Nat.mul rem SC) (dot MVR du.2.1)) ∧ᵇ
    kids ih C RTb H (Nat.sub (sel (Nat.ble C.N cut) C.N cut) pos) d pl MV MVR fx.2.1 fx.2.2.1 pos fx.2.2.2

/-- the stream after the branch header up to the dual: `S4` (`cut`, `kind`, optional row, `hd` read) -/
@[inline] def brS4 (S1 : Nat) : Nat := sk 1 (sel (Nat.beq (rd 2 (sk 7 S1)) 1) (sk 12 (sk 9 S1)) (sk 9 S1))
/-- the node dual flag -/
@[inline] def brHd (S1 : Nat) : Bool := Nat.beq (rd 1 (sel (Nat.beq (rd 2 (sk 7 S1)) 1) (sk 12 (sk 9 S1)) (sk 9 S1))) 1
/-- the node dual (or the empty dual) -/
@[inline] def brDu (RTb S1 : Nat) : Nat × Nat × Nat := sel (brHd S1) (rdual RTb (rd 8 (brS4 S1)) (sk 8 (brS4 S1))) (0, 0, brS4 S1)

/-- one node (`ih`: the node checker with one less fuel) -/
def nodeStep (C : Ctx) (RTb H : Nat) (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (d pos pl MV MVR UF UFR S : Nat) : Bool :=
  sel (Nat.beq (rd 2 S) 0)
    (Nat.beq (Nat.sub C.R d) 0 ∧ᵇ leafOK C pl)
    (Nat.ble 1 (Nat.sub C.R d) ∧ᵇ
      sel (Nat.beq (rd 2 S) 1)
        (Nat.blt (Nat.add (rdual RTb (rd 8 (sk 2 S)) (sk 8 (sk 2 S))).1 (deficit (rdual RTb (rd 8 (sk 2 S)) (sk 8 (sk 2 S))).2.1 UFR pos))
          (Nat.add (Nat.mul (Nat.sub C.R d) SC) (dot MVR (rdual RTb (rd 8 (sk 2 S)) (sk 8 (sk 2 S))).2.1)))
        (branchT ih C RTb H d pos pl MV MVR UFR (Nat.sub C.R d) (rd 7 (sk 2 S)) (rd 2 (sk 7 (sk 2 S))) (rd 12 (sk 9 (sk 2 S)))
          (brHd (sk 2 S)) (brDu RTb (sk 2 S))
          (sel (brHd (sk 2 S))
            (fixes (rd 7 (brDu RTb (sk 2 S)).2.2) (brDu RTb (sk 2 S)).2.1
              (Nat.sub (Nat.add (brDu RTb (sk 2 S)).1 (deficit (brDu RTb (sk 2 S)).2.1 UFR pos))
                (Nat.add (Nat.mul (Nat.sub C.R d) SC) (dot MVR (brDu RTb (sk 2 S)).2.1)))
              UF UFR (sk 7 (brDu RTb (sk 2 S)).2.2))
            (true, UF, UFR, brS4 (sk 2 S)))))

/-- the node checker with `fuel` levels -/
def node (C : Ctx) (RTb H fuel : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ _ _ _ _ => false)
    (fun _ ih d pos pl MV MVR UF UFR S => nodeStep C RTb H ih d pos pl MV MVR UF UFR S)
    fuel

/-- the header's delegated states: `(nd, H, rest)` -/
@[inline] def hdr (S : Nat) : Nat × Nat × Nat :=
  (rd 8 S, rd (Nat.mul 695 (rd 8 S)) (sk 8 S), sk (Nat.add 8 (Nat.mul 695 (rd 8 S))) S)

/-- prefix multiplicities `(MV, MVR)` of the `d` labels in `pl` -/
def mvOf (d pl : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun MV MVR _ => (MV, MVR))
    (fun _ ih MV MVR pl => ih (Nat.add MV (one (rd 7 pl))) (Nat.add MVR (oner (rd 7 pl))) (sk 7 pl)) d 0 0 pl

/-! ## Blocks -/

/-- the block's depth -/
@[inline] def bD (S : Nat) : Nat := rd 5 (sk 1 S)
/-- the block's prefix labels (`[7]` each) -/
@[inline] def bPl (S : Nat) : Nat := rd (Nat.mul 7 (bD S)) (sk 13 S)
/-- the stream after the prefix -/
@[inline] def bS1 (S : Nat) : Nat := sk (Nat.add 13 (Nat.mul 7 (bD S))) S
/-- the stream after the budgets (mode 1: `127 × [4]`) -/
@[inline] def bS2 (S : Nat) : Nat := sel (Nat.beq (rd 1 S) 1) (sk 508 (bS1 S)) (bS1 S)
/-- the block's row table and the rest of the stream -/
@[inline] def bRT (sl : Nat → Nat) (S : Nat) : Nat × Nat := mkRT sl (rd 12 (hdr (bS2 S)).2.2) (sk 12 (hdr (bS2 S)).2.2)
/-- the start budgets: mode 1 explicit, mode 0 the label caps minus the prefix -/
@[inline] def bUF (UB S : Nat) : Nat := sel (Nat.beq (rd 1 S) 1) (budU (bS1 S)) (Nat.sub UB (mvOf (bD S) (bPl S)).1)
@[inline] def bUFR (UBR S : Nat) : Nat := sel (Nat.beq (rd 1 S) 1) (budUR (bS1 S)) (Nat.sub UBR (mvOf (bD S) (bPl S)).2)
/-- mode 0: the rows saturated at the start -/
@[inline] def bSat (sl : Nat → Nat) (UB UBR S : Nat) : Bool × Nat × Nat × Nat :=
  sel (Nat.beq (rd 1 S) 0)
    (sats (bRT sl S).1 (rd 8 (bRT sl S).2) (mvOf (bD S) (bPl S)).1 (bUF UB S) (bUFR UBR S) (sk 8 (bRT sl S).2))
    (true, bUF UB S, bUFR UBR S, (bRT sl S).2)

/-- a block (see the module docstring) -/
def block (C : Ctx) (sl : Nat → Nat) (UB UBR S : Nat) : Bool :=
  (bSat sl UB UBR S).1 ∧ᵇ Nat.ble (bD S) C.R ∧ᵇ
    node C (bRT sl S).1 (hdr (bS2 S)).2.1 32 (bD S) (rd 7 (sk 6 S)) (bPl S) (mvOf (bD S) (bPl S)).1 (mvOf (bD S) (bPl S)).2
      (bSat sl UB UBR S).2.1 (bSat sl UB UBR S).2.2.1 (bSat sl UB UBR S).2.2.2

/-- the block `Sc` starts (mode 1) in the state recorded as `r` (`12 + 7 d + 508` bits after the mode bit) -/
def glue (r Sc : Nat) : Bool :=
  Nat.beq (rd 1 Sc) 1 ∧ᵇ Nat.beq (rd (Nat.add 520 (Nat.mul 7 (rd 5 r))) (sk 1 Sc)) r

/-- the block `Sc` is a mode-0 block (a search job: budgets from the label caps) with the prefix recorded as `r`
(depth, position, labels); the recorded budgets are not needed -/
def glue0 (r Sc : Nat) : Bool :=
  Nat.beq (rd 1 Sc) 0 ∧ᵇ Nat.beq (rd (Nat.add 12 (Nat.mul 7 (rd 5 r))) (sk 1 Sc)) (rd (Nat.add 12 (Nat.mul 7 (rd 5 r))) r)

end
end B334.E1x.E1G
