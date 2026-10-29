import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2196L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2196 of `S707`, parts 0 … 96, re-packed by predicted kernel memory (2.87 of 8.19 GB;
stage707_v5; the theorems are v3's `K2196C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2196_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2196.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2196_0 : IPChk.allR (Pts.glueIB K2196.lits KW_2196) 0 1 = true := by decide +kernel
theorem kb_2196_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2196.lits.getD i 0)) 1 10 = true := by
  decide +kernel
theorem kg_2196_1 : IPChk.allR (Pts.glueIB K2196.lits KW_2196) 1 10 = true := by decide +kernel
theorem kb_2196_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2196.lits.getD i 0)) 11 55 = true := by
  decide +kernel
theorem kg_2196_11 : IPChk.allR (Pts.glueIB K2196.lits KW_2196) 11 55 = true := by decide +kernel
theorem kb_2196_66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2196.lits.getD i 0)) 66 31 = true := by
  decide +kernel
theorem kg_2196_66 : IPChk.allR (Pts.glueIB K2196.lits KW_2196) 66 31 = true := by decide +kernel

end B334.E1x.Pts.S707
