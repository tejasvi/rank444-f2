import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2132L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2132 of `S707`, parts 0 … 107, re-packed by predicted kernel memory (4.42 of 8.19 GB;
stage707_v5; the theorems are v3's `K2132C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2132_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_2132_0 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 0 5 = true := by decide +kernel
theorem kb_2132_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 5 8 = true := by
  decide +kernel
theorem kg_2132_5 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 5 8 = true := by decide +kernel
theorem kb_2132_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 13 7 = true := by
  decide +kernel
theorem kg_2132_13 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 13 7 = true := by decide +kernel
theorem kb_2132_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 20 7 = true := by
  decide +kernel
theorem kg_2132_20 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 20 7 = true := by decide +kernel
theorem kb_2132_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 27 32 = true := by
  decide +kernel
theorem kg_2132_27 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 27 32 = true := by decide +kernel
theorem kb_2132_59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2132.lits.getD i 0)) 59 49 = true := by
  decide +kernel
theorem kg_2132_59 : IPChk.allR (Pts.glueIB K2132.lits KW_2132) 59 49 = true := by decide +kernel

end B334.E1x.Pts.S707
