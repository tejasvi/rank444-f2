import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4639L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4639 of `S707`, parts 28 … 36, re-packed by predicted kernel memory (4.11 of 8.19 GB;
stage707_v5; the theorems are v3's `K4639C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4639_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 28 2 = true := by
  decide +kernel
theorem kg_4639_28 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 28 2 = true := by decide +kernel
theorem kb_4639_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 30 2 = true := by
  decide +kernel
theorem kg_4639_30 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 30 2 = true := by decide +kernel
theorem kb_4639_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 32 2 = true := by
  decide +kernel
theorem kg_4639_32 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 32 2 = true := by decide +kernel
theorem kb_4639_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 34 1 = true := by
  decide +kernel
theorem kg_4639_34 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 34 1 = true := by decide +kernel
theorem kb_4639_35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 35 1 = true := by
  decide +kernel
theorem kg_4639_35 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 35 1 = true := by decide +kernel
theorem kb_4639_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4639.lits.getD i 0)) 36 1 = true := by
  decide +kernel
theorem kg_4639_36 : IPChk.allR (Pts.glueIB K4639.lits KW_4639) 36 1 = true := by decide +kernel

end B334.E1x.Pts.S707
