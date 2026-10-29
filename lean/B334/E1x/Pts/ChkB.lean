import B334.E1x.CheckP
import B334.E1x.IPChk

/-! # Core-Lean Boolean checks for the point-run assembly

The generated check modules evaluate these by `decide +kernel` in core Lean (a baseline of ~1.5 GB instead of the
~6.5 GB of the Mathlib-sized soundness modules); `Pts/JobS.lean` turns them into the hypotheses of the
composition theorems (`P/Asm.lean`, `P/Hdr.lean`). Each definition repeats the body of its `E1PS` counterpart, so
the two are equal by `rfl` (`recB` = `recOf`, `glue1B` = `glue1`, `glue1FB` = `glue1F`; the loops `glueIB`,
`glueWB` are the inner loops of `glueChk`, `glueChkW`).

* `jobB C sl UB UBR H L W`: a search job given as the list `L` of its pieces: every piece is accepted, every header
  record of piece `i` is glued to the later piece `W[i][j]` of `L`, and the first piece is a mode-0 block whose
  `14 + 8 d`-bit header is `H` (its entry in the run's job header table).
* `glueWB Ss nJ Jf Wf i`: the header records of block `i` of the top chain `Ss` are glued as `Wf i j` says (a later
  block of `Ss`, or job `Wf i j - |Ss|` of the header table `Jf`). -/

namespace B334.E1x.Pts

noncomputable section

/-- record `j` of block `S` (as `E1PS.recOf`) -/
def recB (S j : Nat) : Nat := (E1P.hdr (E1P.bS2 S)).2.1 / 2 ^ (1233 * j) % 2 ^ 1233

/-- record `j` of block `i` of `L` is glued to the later block `w` of `L` (as `E1PS.glue1`) -/
def glue1B (L : List Nat) (i j w : Nat) : Bool :=
  Nat.blt i w && Nat.blt w L.length &&
    (E1P.glue (recB (L.getD i 0) j) (L.getD w 0) || E1P.glue0 (recB (L.getD i 0) j) (L.getD w 0))

/-- the header records of block `i` of `L` are glued as `W` says (the inner loop of `E1PS.glueChk`) -/
def glueIB (L : List Nat) (W : List (List Nat)) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1B L i j ((W.getD i []).getD j 0))
    (E1P.rd 8 (E1P.bS2 (L.getD i 0)))

/-- a search job: the pieces `L` pass and are glued inside (`W`), and the first piece is a mode-0 block with
header `H` -/
def jobB (C : E1P.Ctx) (sl : Nat → Nat) (UB UBR H : Nat) (L : List Nat) (W : List (List Nat)) : Bool :=
  Nat.blt 0 L.length &&
  IPChk.allR (fun i => E1P.block C sl UB UBR (L.getD i 0)) 0 L.length &&
  IPChk.allR (glueIB L W) 0 L.length &&
  Nat.beq (L.getD 0 0 % 2) 0 &&
  Nat.beq H (L.getD 0 0 % 2 ^ (14 + 8 * (L.getD 0 0 / 2 % 2 ^ 5)))

/-- record `j` of block `i` of the top chain `Ss` is glued to `w`: a later block of `Ss` (`w < |Ss|`) or job
`w - |Ss|` of `Jf` (as `E1PS.glue1F`) -/
def glue1FB (Ss : List Nat) (nJ : Nat) (Jf : Nat → Nat) (i j w : Nat) : Bool :=
  cond (Nat.blt w Ss.length) (glue1B Ss i j w)
    (Nat.blt (w - Ss.length) nJ &&
      (E1P.glue (recB (Ss.getD i 0) j) (Jf (w - Ss.length)) || E1P.glue0 (recB (Ss.getD i 0) j) (Jf (w - Ss.length))))

/-- the header records of block `i` of the top chain (the inner loop of `E1PS.glueChkW`) -/
def glueWB (Ss : List Nat) (nJ : Nat) (Jf : Nat → Nat) (Wf : Nat → Nat → Nat) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1FB Ss nJ Jf i j (Wf i j))
    (E1P.rd 8 (E1P.bS2 (Ss.getD i 0)))

end

end B334.E1x.Pts
