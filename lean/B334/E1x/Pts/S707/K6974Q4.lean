import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6974L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6974 of `S707`, parts 437 … 475, re-packed by predicted kernel memory (2.71 of 8.19 GB;
stage707_v5; the theorems are v3's `K6974C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6974_437 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 437 12 = true := by
  decide +kernel
theorem kg_6974_437 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 437 12 = true := by decide +kernel
theorem kb_6974_449 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 449 4 = true := by
  decide +kernel
theorem kg_6974_449 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 449 4 = true := by decide +kernel
theorem kb_6974_453 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 453 12 = true := by
  decide +kernel
theorem kg_6974_453 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 453 12 = true := by decide +kernel
theorem kb_6974_465 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 465 11 = true := by
  decide +kernel
theorem kg_6974_465 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 465 11 = true := by decide +kernel

end B334.E1x.Pts.S707
