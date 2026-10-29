import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6682L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6682 of `S707`, parts 202 … 300, re-packed by predicted kernel memory (3.11 of 8.19 GB;
stage707_v5; the theorems are v3's `K6682C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6682_202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6682.lits.getD i 0)) 202 6 = true := by
  decide +kernel
theorem kg_6682_202 : IPChk.allR (Pts.glueIB K6682.lits KW_6682) 202 6 = true := by decide +kernel
theorem kb_6682_208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6682.lits.getD i 0)) 208 16 = true := by
  decide +kernel
theorem kg_6682_208 : IPChk.allR (Pts.glueIB K6682.lits KW_6682) 208 16 = true := by decide +kernel
theorem kb_6682_224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6682.lits.getD i 0)) 224 62 = true := by
  decide +kernel
theorem kg_6682_224 : IPChk.allR (Pts.glueIB K6682.lits KW_6682) 224 62 = true := by decide +kernel
theorem kb_6682_286 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6682.lits.getD i 0)) 286 15 = true := by
  decide +kernel
theorem kg_6682_286 : IPChk.allR (Pts.glueIB K6682.lits KW_6682) 286 15 = true := by decide +kernel

end B334.E1x.Pts.S707
