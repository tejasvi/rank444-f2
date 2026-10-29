import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2661L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2661 of `S707`, parts 126 … 301, re-packed by predicted kernel memory (4.66 of 8.19 GB;
stage707_v5; the theorems are v3's `K2661C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2661_126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 126 8 = true := by
  decide +kernel
theorem kg_2661_126 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 126 8 = true := by decide +kernel
theorem kb_2661_134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 134 53 = true := by
  decide +kernel
theorem kg_2661_134 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 134 53 = true := by decide +kernel
theorem kb_2661_187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 187 24 = true := by
  decide +kernel
theorem kg_2661_187 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 187 24 = true := by decide +kernel
theorem kb_2661_211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 211 31 = true := by
  decide +kernel
theorem kg_2661_211 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 211 31 = true := by decide +kernel
theorem kb_2661_242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 242 38 = true := by
  decide +kernel
theorem kg_2661_242 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 242 38 = true := by decide +kernel
theorem kb_2661_280 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2661.lits.getD i 0)) 280 22 = true := by
  decide +kernel
theorem kg_2661_280 : IPChk.allR (Pts.glueIB K2661.lits KW_2661) 280 22 = true := by decide +kernel

end B334.E1x.Pts.S707
