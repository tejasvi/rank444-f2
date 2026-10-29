import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2561L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2561 of `S707`, parts 0 … 69, re-packed by predicted kernel memory (4.70 of 8.19 GB;
stage707_v5; the theorems are v3's `K2561C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2561_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2561_0 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 2 = true := by decide +kernel
theorem kb_2561_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 2 13 = true := by
  decide +kernel
theorem kg_2561_2 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 2 13 = true := by decide +kernel
theorem kb_2561_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 15 13 = true := by
  decide +kernel
theorem kg_2561_15 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 15 13 = true := by decide +kernel
theorem kb_2561_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 28 23 = true := by
  decide +kernel
theorem kg_2561_28 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 28 23 = true := by decide +kernel
theorem kb_2561_51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 51 19 = true := by
  decide +kernel
theorem kg_2561_51 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 51 19 = true := by decide +kernel

end B334.E1x.Pts.S707
