import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2570L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2570 of `S707`, parts 287 … 329, re-packed by predicted kernel memory (2.35 of 8.19 GB;
stage707_v5; the theorems are v3's `K2570C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2570_287 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2570.lits.getD i 0)) 287 11 = true := by
  decide +kernel
theorem kg_2570_287 : IPChk.allR (Pts.glueIB K2570.lits KW_2570) 287 11 = true := by decide +kernel
theorem kb_2570_298 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2570.lits.getD i 0)) 298 18 = true := by
  decide +kernel
theorem kg_2570_298 : IPChk.allR (Pts.glueIB K2570.lits KW_2570) 298 18 = true := by decide +kernel
theorem kb_2570_316 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2570.lits.getD i 0)) 316 7 = true := by
  decide +kernel
theorem kg_2570_316 : IPChk.allR (Pts.glueIB K2570.lits KW_2570) 316 7 = true := by decide +kernel
theorem kb_2570_323 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2570.lits.getD i 0)) 323 7 = true := by
  decide +kernel
theorem kg_2570_323 : IPChk.allR (Pts.glueIB K2570.lits KW_2570) 323 7 = true := by decide +kernel

end B334.E1x.Pts.S707
