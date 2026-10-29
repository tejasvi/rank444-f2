import B334.E1x.CheckG
import B334.E1x.IPChk

/-! # Core-Lean Boolean checks for the assembly of multi-block E1G runs

E1G copy of `Pts/ChkB.lean` (E1P widths 1233 / `14 + 8 d` replaced by the E1G 695 / `13 + 7 d`). The
generated check modules evaluate these by `decide +kernel` in core Lean; `GJ/JobS.lean` turns them into the hypotheses
of the composition theorems of `G/Asm.lean` and `G/Hdr.lean`. Each definition repeats the body of its `E1GS`
counterpart, so the two are equal by `rfl` (`recB` = `recOf`, `glue1B` = `glue1`, `glue1FB` = `glue1F`; the loops
`glueIB`, `glueWB` are the inner loops of `glueChk`, `glueChkW`).

* `jobB C sl UB UBR H L W`: a search job given as the list `L` of its pieces: every piece is accepted, every header
  record of piece `i` is glued to the later piece `W[i][j]` of `L`, and the first piece is a mode-0 block whose
  `13 + 7 d`-bit header is `H` (its entry in the run's job header table).
* `glueWB Ss nJ Jf Wf i`: the header records of block `i` of the top chain `Ss` are glued as `Wf i j` says (a later
  block of `Ss`, or job `Wf i j - |Ss|` of the header table `Jf`). -/

namespace B334.E1x.GJ

noncomputable section

/-- record `j` of block `S` (as `E1GS.recOf`) -/
def recB (S j : Nat) : Nat := (E1G.hdr (E1G.bS2 S)).2.1 / 2 ^ (695 * j) % 2 ^ 695

/-- record `j` of block `i` of `L` is glued to the later block `w` of `L` (as `E1GS.glue1`) -/
def glue1B (L : List Nat) (i j w : Nat) : Bool :=
  Nat.blt i w && Nat.blt w L.length &&
    (E1G.glue (recB (L.getD i 0) j) (L.getD w 0) || E1G.glue0 (recB (L.getD i 0) j) (L.getD w 0))

/-- the header records of block `i` of `L` are glued as `W` says (the inner loop of `E1GS.glueChk`) -/
def glueIB (L : List Nat) (W : List (List Nat)) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1B L i j ((W.getD i []).getD j 0))
    (E1G.rd 8 (E1G.bS2 (L.getD i 0)))

/-- a search job: the pieces `L` pass and are glued inside (`W`), and the first piece is a mode-0 block with
header `H` -/
def jobB (C : E1G.Ctx) (sl : Nat → Nat) (UB UBR H : Nat) (L : List Nat) (W : List (List Nat)) : Bool :=
  Nat.blt 0 L.length &&
  IPChk.allR (fun i => E1G.block C sl UB UBR (L.getD i 0)) 0 L.length &&
  IPChk.allR (glueIB L W) 0 L.length &&
  Nat.beq (L.getD 0 0 % 2) 0 &&
  Nat.beq H (L.getD 0 0 % 2 ^ (13 + 7 * (L.getD 0 0 / 2 % 2 ^ 5)))

/-- record `j` of block `i` of the top chain `Ss` is glued to `w`: a later block of `Ss` (`w < |Ss|`) or job
`w - |Ss|` of `Jf` (as `E1GS.glue1F`) -/
def glue1FB (Ss : List Nat) (nJ : Nat) (Jf : Nat → Nat) (i j w : Nat) : Bool :=
  cond (Nat.blt w Ss.length) (glue1B Ss i j w)
    (Nat.blt (w - Ss.length) nJ &&
      (E1G.glue (recB (Ss.getD i 0) j) (Jf (w - Ss.length)) || E1G.glue0 (recB (Ss.getD i 0) j) (Jf (w - Ss.length))))

/-- the header records of block `i` of the top chain (the inner loop of `E1GS.glueChkW`) -/
def glueWB (Ss : List Nat) (nJ : Nat) (Jf : Nat → Nat) (Wf : Nat → Nat → Nat) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1FB Ss nJ Jf i j (Wf i j))
    (E1G.rd 8 (E1G.bS2 (Ss.getD i 0)))

end

end B334.E1x.GJ
