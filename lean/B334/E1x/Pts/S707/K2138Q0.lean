import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2138L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2138 of `S707`, parts 0 … 117, re-packed by predicted kernel memory (4.88 of 8.19 GB;
stage707_v5; the theorems are v3's `K2138C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2138_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2138_0 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 0 2 = true := by decide +kernel
theorem kb_2138_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 2 8 = true := by
  decide +kernel
theorem kg_2138_2 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 2 8 = true := by decide +kernel
theorem kb_2138_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 10 7 = true := by
  decide +kernel
theorem kg_2138_10 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 10 7 = true := by decide +kernel
theorem kb_2138_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 17 9 = true := by
  decide +kernel
theorem kg_2138_17 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 17 9 = true := by decide +kernel
theorem kb_2138_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 26 38 = true := by
  decide +kernel
theorem kg_2138_26 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 26 38 = true := by decide +kernel
theorem kb_2138_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 64 40 = true := by
  decide +kernel
theorem kg_2138_64 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 64 40 = true := by decide +kernel
theorem kb_2138_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2138.lits.getD i 0)) 104 14 = true := by
  decide +kernel
theorem kg_2138_104 : IPChk.allR (Pts.glueIB K2138.lits KW_2138) 104 14 = true := by decide +kernel

end B334.E1x.Pts.S707
