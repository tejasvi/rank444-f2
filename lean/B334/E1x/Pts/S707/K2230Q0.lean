import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2230L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2230 of `S707`, parts 0 … 71, re-packed by predicted kernel memory (3.40 of 8.19 GB;
stage707_v5; the theorems are v3's `K2230C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2230_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2230.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_2230_0 : IPChk.allR (Pts.glueIB K2230.lits KW_2230) 0 6 = true := by decide +kernel
theorem kb_2230_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2230.lits.getD i 0)) 6 7 = true := by
  decide +kernel
theorem kg_2230_6 : IPChk.allR (Pts.glueIB K2230.lits KW_2230) 6 7 = true := by decide +kernel
theorem kb_2230_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2230.lits.getD i 0)) 13 30 = true := by
  decide +kernel
theorem kg_2230_13 : IPChk.allR (Pts.glueIB K2230.lits KW_2230) 13 30 = true := by decide +kernel
theorem kb_2230_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2230.lits.getD i 0)) 43 27 = true := by
  decide +kernel
theorem kg_2230_43 : IPChk.allR (Pts.glueIB K2230.lits KW_2230) 43 27 = true := by decide +kernel
theorem kb_2230_70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2230.lits.getD i 0)) 70 2 = true := by
  decide +kernel
theorem kg_2230_70 : IPChk.allR (Pts.glueIB K2230.lits KW_2230) 70 2 = true := by decide +kernel

end B334.E1x.Pts.S707
