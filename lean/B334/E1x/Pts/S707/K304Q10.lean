import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K304L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 304 of `S707`, parts 944 … 1044, re-packed by predicted kernel memory (4.77 of 8.19 GB;
stage707_v5; the theorems are v3's `K304C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_304_944 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 944 3 = true := by
  decide +kernel
theorem kg_304_944 : IPChk.allR (Pts.glueIB K304.lits KW_304) 944 3 = true := by decide +kernel
theorem kb_304_947 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 947 10 = true := by
  decide +kernel
theorem kg_304_947 : IPChk.allR (Pts.glueIB K304.lits KW_304) 947 10 = true := by decide +kernel
theorem kb_304_957 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 957 7 = true := by
  decide +kernel
theorem kg_304_957 : IPChk.allR (Pts.glueIB K304.lits KW_304) 957 7 = true := by decide +kernel
theorem kb_304_964 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 964 2 = true := by
  decide +kernel
theorem kg_304_964 : IPChk.allR (Pts.glueIB K304.lits KW_304) 964 2 = true := by decide +kernel
theorem kb_304_966 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 966 29 = true := by
  decide +kernel
theorem kg_304_966 : IPChk.allR (Pts.glueIB K304.lits KW_304) 966 29 = true := by decide +kernel
theorem kb_304_995 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 995 33 = true := by
  decide +kernel
theorem kg_304_995 : IPChk.allR (Pts.glueIB K304.lits KW_304) 995 33 = true := by decide +kernel
theorem kb_304_1028 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 1028 17 = true := by
  decide +kernel
theorem kg_304_1028 : IPChk.allR (Pts.glueIB K304.lits KW_304) 1028 17 = true := by decide +kernel

end B334.E1x.Pts.S707
