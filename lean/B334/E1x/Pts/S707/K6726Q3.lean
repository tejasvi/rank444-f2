import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6726L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6726 of `S707`, parts 251 … 367, re-packed by predicted kernel memory (3.66 of 8.19 GB;
stage707_v5; the theorems are v3's `K6726C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6726_251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6726.lits.getD i 0)) 251 36 = true := by
  decide +kernel
theorem kg_6726_251 : IPChk.allR (Pts.glueIB K6726.lits KW_6726) 251 36 = true := by decide +kernel
theorem kb_6726_287 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6726.lits.getD i 0)) 287 42 = true := by
  decide +kernel
theorem kg_6726_287 : IPChk.allR (Pts.glueIB K6726.lits KW_6726) 287 42 = true := by decide +kernel
theorem kb_6726_329 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6726.lits.getD i 0)) 329 6 = true := by
  decide +kernel
theorem kg_6726_329 : IPChk.allR (Pts.glueIB K6726.lits KW_6726) 329 6 = true := by decide +kernel
theorem kb_6726_335 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6726.lits.getD i 0)) 335 5 = true := by
  decide +kernel
theorem kg_6726_335 : IPChk.allR (Pts.glueIB K6726.lits KW_6726) 335 5 = true := by decide +kernel
theorem kb_6726_340 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6726.lits.getD i 0)) 340 28 = true := by
  decide +kernel
theorem kg_6726_340 : IPChk.allR (Pts.glueIB K6726.lits KW_6726) 340 28 = true := by decide +kernel

end B334.E1x.Pts.S707
