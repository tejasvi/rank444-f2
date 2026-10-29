import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K366L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 366 of `S707`, parts 544 … 596, re-packed by predicted kernel memory (3.93 of 8.19 GB;
stage707_v5; the theorems are v3's `K366C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_366_544 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 544 3 = true := by
  decide +kernel
theorem kg_366_544 : IPChk.allR (Pts.glueIB K366.lits KW_366) 544 3 = true := by decide +kernel
theorem kb_366_547 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 547 7 = true := by
  decide +kernel
theorem kg_366_547 : IPChk.allR (Pts.glueIB K366.lits KW_366) 547 7 = true := by decide +kernel
theorem kb_366_554 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 554 2 = true := by
  decide +kernel
theorem kg_366_554 : IPChk.allR (Pts.glueIB K366.lits KW_366) 554 2 = true := by decide +kernel
theorem kb_366_556 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 556 3 = true := by
  decide +kernel
theorem kg_366_556 : IPChk.allR (Pts.glueIB K366.lits KW_366) 556 3 = true := by decide +kernel
theorem kb_366_559 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 559 38 = true := by
  decide +kernel
theorem kg_366_559 : IPChk.allR (Pts.glueIB K366.lits KW_366) 559 38 = true := by decide +kernel

end B334.E1x.Pts.S707
