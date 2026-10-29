import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5222L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5222 of `S707`, parts 0 … 39, re-packed by predicted kernel memory (3.85 of 8.19 GB;
stage707_v5; the theorems are v3's `K5222C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5222_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_5222_0 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 0 1 = true := by decide +kernel
theorem kb_5222_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_5222_1 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 1 1 = true := by decide +kernel
theorem kb_5222_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 2 7 = true := by
  decide +kernel
theorem kg_5222_2 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 2 7 = true := by decide +kernel
theorem kb_5222_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 9 11 = true := by
  decide +kernel
theorem kg_5222_9 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 9 11 = true := by decide +kernel
theorem kb_5222_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 20 5 = true := by
  decide +kernel
theorem kg_5222_20 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 20 5 = true := by decide +kernel
theorem kb_5222_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5222.lits.getD i 0)) 25 15 = true := by
  decide +kernel
theorem kg_5222_25 : IPChk.allR (Pts.glueIB K5222.lits KW_5222) 25 15 = true := by decide +kernel

end B334.E1x.Pts.S707
