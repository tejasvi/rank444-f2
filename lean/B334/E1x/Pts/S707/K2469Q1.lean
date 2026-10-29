import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2469L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2469 of `S707`, parts 122 … 210, re-packed by predicted kernel memory (3.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K2469C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2469_122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 122 49 = true := by
  decide +kernel
theorem kg_2469_122 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 122 49 = true := by decide +kernel
theorem kb_2469_171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 171 18 = true := by
  decide +kernel
theorem kg_2469_171 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 171 18 = true := by decide +kernel
theorem kb_2469_189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 189 7 = true := by
  decide +kernel
theorem kg_2469_189 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 189 7 = true := by decide +kernel
theorem kb_2469_196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 196 1 = true := by
  decide +kernel
theorem kg_2469_196 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 196 1 = true := by decide +kernel
theorem kb_2469_197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 197 14 = true := by
  decide +kernel
theorem kg_2469_197 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 197 14 = true := by decide +kernel

end B334.E1x.Pts.S707
