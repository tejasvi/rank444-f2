import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2608L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2608 of `S707`, parts 329 … 430, re-packed by predicted kernel memory (3.20 of 8.19 GB;
stage707_v5; the theorems are v3's `K2608C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2608_329 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2608.lits.getD i 0)) 329 55 = true := by
  decide +kernel
theorem kg_2608_329 : IPChk.allR (Pts.glueIB K2608.lits KW_2608) 329 55 = true := by decide +kernel
theorem kb_2608_384 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2608.lits.getD i 0)) 384 1 = true := by
  decide +kernel
theorem kg_2608_384 : IPChk.allR (Pts.glueIB K2608.lits KW_2608) 384 1 = true := by decide +kernel
theorem kb_2608_385 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2608.lits.getD i 0)) 385 3 = true := by
  decide +kernel
theorem kg_2608_385 : IPChk.allR (Pts.glueIB K2608.lits KW_2608) 385 3 = true := by decide +kernel
theorem kb_2608_388 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2608.lits.getD i 0)) 388 23 = true := by
  decide +kernel
theorem kg_2608_388 : IPChk.allR (Pts.glueIB K2608.lits KW_2608) 388 23 = true := by decide +kernel
theorem kb_2608_411 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2608.lits.getD i 0)) 411 20 = true := by
  decide +kernel
theorem kg_2608_411 : IPChk.allR (Pts.glueIB K2608.lits KW_2608) 411 20 = true := by decide +kernel

end B334.E1x.Pts.S707
