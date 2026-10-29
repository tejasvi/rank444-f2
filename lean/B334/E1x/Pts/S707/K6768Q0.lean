import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6768L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6768 of `S707`, parts 0 … 48, re-packed by predicted kernel memory (4.75 of 8.19 GB;
stage707_v5; the theorems are v3's `K6768C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6768_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_6768_0 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 0 3 = true := by decide +kernel
theorem kb_6768_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 3 2 = true := by
  decide +kernel
theorem kg_6768_3 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 3 2 = true := by decide +kernel
theorem kb_6768_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 5 11 = true := by
  decide +kernel
theorem kg_6768_5 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 5 11 = true := by decide +kernel
theorem kb_6768_16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 16 3 = true := by
  decide +kernel
theorem kg_6768_16 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 16 3 = true := by decide +kernel
theorem kb_6768_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 19 5 = true := by
  decide +kernel
theorem kg_6768_19 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 19 5 = true := by decide +kernel
theorem kb_6768_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 24 8 = true := by
  decide +kernel
theorem kg_6768_24 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 24 8 = true := by decide +kernel
theorem kb_6768_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6768.lits.getD i 0)) 32 17 = true := by
  decide +kernel
theorem kg_6768_32 : IPChk.allR (Pts.glueIB K6768.lits KW_6768) 32 17 = true := by decide +kernel

end B334.E1x.Pts.S707
