import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2264L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2264 of `S707`, parts 0 … 112, re-packed by predicted kernel memory (3.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K2264C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2264_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2264.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2264_0 : IPChk.allR (Pts.glueIB K2264.lits KW_2264) 0 1 = true := by decide +kernel
theorem kb_2264_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2264.lits.getD i 0)) 1 12 = true := by
  decide +kernel
theorem kg_2264_1 : IPChk.allR (Pts.glueIB K2264.lits KW_2264) 1 12 = true := by decide +kernel
theorem kb_2264_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2264.lits.getD i 0)) 13 56 = true := by
  decide +kernel
theorem kg_2264_13 : IPChk.allR (Pts.glueIB K2264.lits KW_2264) 13 56 = true := by decide +kernel
theorem kb_2264_69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2264.lits.getD i 0)) 69 44 = true := by
  decide +kernel
theorem kg_2264_69 : IPChk.allR (Pts.glueIB K2264.lits KW_2264) 69 44 = true := by decide +kernel

end B334.E1x.Pts.S707
