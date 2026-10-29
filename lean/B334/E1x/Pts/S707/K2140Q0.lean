import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2140L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2140 of `S707`, parts 0 … 94, re-packed by predicted kernel memory (2.82 of 8.19 GB;
stage707_v5; the theorems are v3's `K2140C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2140_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2140.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2140_0 : IPChk.allR (Pts.glueIB K2140.lits KW_2140) 0 1 = true := by decide +kernel
theorem kb_2140_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2140.lits.getD i 0)) 1 11 = true := by
  decide +kernel
theorem kg_2140_1 : IPChk.allR (Pts.glueIB K2140.lits KW_2140) 1 11 = true := by decide +kernel
theorem kb_2140_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2140.lits.getD i 0)) 12 57 = true := by
  decide +kernel
theorem kg_2140_12 : IPChk.allR (Pts.glueIB K2140.lits KW_2140) 12 57 = true := by decide +kernel
theorem kb_2140_69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2140.lits.getD i 0)) 69 26 = true := by
  decide +kernel
theorem kg_2140_69 : IPChk.allR (Pts.glueIB K2140.lits KW_2140) 69 26 = true := by decide +kernel

end B334.E1x.Pts.S707
