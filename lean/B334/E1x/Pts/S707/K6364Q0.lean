import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6364L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6364 of `S707`, parts 0 … 47, re-packed by predicted kernel memory (5.00 of 8.19 GB;
stage707_v5; the theorems are v3's `K6364C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6364_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_6364_0 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 0 6 = true := by decide +kernel
theorem kb_6364_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 6 2 = true := by
  decide +kernel
theorem kg_6364_6 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 6 2 = true := by decide +kernel
theorem kb_6364_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 8 14 = true := by
  decide +kernel
theorem kg_6364_8 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 8 14 = true := by decide +kernel
theorem kb_6364_22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 22 6 = true := by
  decide +kernel
theorem kg_6364_22 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 22 6 = true := by decide +kernel
theorem kb_6364_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 28 11 = true := by
  decide +kernel
theorem kg_6364_28 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 28 11 = true := by decide +kernel
theorem kb_6364_39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 39 2 = true := by
  decide +kernel
theorem kg_6364_39 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 39 2 = true := by decide +kernel
theorem kb_6364_41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6364.lits.getD i 0)) 41 7 = true := by
  decide +kernel
theorem kg_6364_41 : IPChk.allR (Pts.glueIB K6364.lits KW_6364) 41 7 = true := by decide +kernel

end B334.E1x.Pts.S707
