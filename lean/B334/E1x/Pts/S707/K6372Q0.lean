import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6372L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6372 of `S707`, parts 0 … 16, re-packed by predicted kernel memory (2.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K6372C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6372_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6372.lits.getD i 0)) 0 14 = true := by
  decide +kernel
theorem kg_6372_0 : IPChk.allR (Pts.glueIB K6372.lits KW_6372) 0 14 = true := by decide +kernel
theorem kb_6372_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6372.lits.getD i 0)) 14 1 = true := by
  decide +kernel
theorem kg_6372_14 : IPChk.allR (Pts.glueIB K6372.lits KW_6372) 14 1 = true := by decide +kernel
theorem kb_6372_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6372.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_6372_15 : IPChk.allR (Pts.glueIB K6372.lits KW_6372) 15 2 = true := by decide +kernel

end B334.E1x.Pts.S707
