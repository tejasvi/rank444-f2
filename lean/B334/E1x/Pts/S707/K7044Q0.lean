import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7044L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7044 of `S707`, parts 0 … 93, re-packed by predicted kernel memory (4.71 of 8.19 GB;
stage707_v5; the theorems are v3's `K7044C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7044_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_7044_0 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 11 = true := by decide +kernel
theorem kb_7044_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 11 2 = true := by
  decide +kernel
theorem kg_7044_11 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 11 2 = true := by decide +kernel
theorem kb_7044_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 13 13 = true := by
  decide +kernel
theorem kg_7044_13 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 13 13 = true := by decide +kernel
theorem kb_7044_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 26 10 = true := by
  decide +kernel
theorem kg_7044_26 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 26 10 = true := by decide +kernel
theorem kb_7044_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 36 24 = true := by
  decide +kernel
theorem kg_7044_36 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 36 24 = true := by decide +kernel
theorem kb_7044_60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 60 34 = true := by
  decide +kernel
theorem kg_7044_60 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 60 34 = true := by decide +kernel

end B334.E1x.Pts.S707
