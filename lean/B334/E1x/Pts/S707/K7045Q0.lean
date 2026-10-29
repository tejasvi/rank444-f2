import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7045L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7045 of `S707`, parts 0 … 98, re-packed by predicted kernel memory (5.07 of 8.19 GB;
stage707_v5; the theorems are v3's `K7045C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7045_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_7045_0 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 11 = true := by decide +kernel
theorem kb_7045_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 11 2 = true := by
  decide +kernel
theorem kg_7045_11 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 11 2 = true := by decide +kernel
theorem kb_7045_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 13 14 = true := by
  decide +kernel
theorem kg_7045_13 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 13 14 = true := by decide +kernel
theorem kb_7045_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 27 5 = true := by
  decide +kernel
theorem kg_7045_27 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 27 5 = true := by decide +kernel
theorem kb_7045_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 32 17 = true := by
  decide +kernel
theorem kg_7045_32 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 32 17 = true := by decide +kernel
theorem kb_7045_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 49 31 = true := by
  decide +kernel
theorem kg_7045_49 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 49 31 = true := by decide +kernel
theorem kb_7045_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 80 19 = true := by
  decide +kernel
theorem kg_7045_80 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 80 19 = true := by decide +kernel

end B334.E1x.Pts.S707
