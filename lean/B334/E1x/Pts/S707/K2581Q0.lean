import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2581L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2581 of `S707`, parts 0 … 77, re-packed by predicted kernel memory (5.73 of 8.19 GB;
stage707_v5; the theorems are v3's `K2581C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2581_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2581_0 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 0 2 = true := by decide +kernel
theorem kb_2581_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_2581_2 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 2 6 = true := by decide +kernel
theorem kb_2581_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 8 17 = true := by
  decide +kernel
theorem kg_2581_8 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 8 17 = true := by decide +kernel
theorem kb_2581_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 25 11 = true := by
  decide +kernel
theorem kg_2581_25 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 25 11 = true := by decide +kernel
theorem kb_2581_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 36 23 = true := by
  decide +kernel
theorem kg_2581_36 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 36 23 = true := by decide +kernel
theorem kb_2581_59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 59 3 = true := by
  decide +kernel
theorem kg_2581_59 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 59 3 = true := by decide +kernel
theorem kb_2581_62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2581.lits.getD i 0)) 62 16 = true := by
  decide +kernel
theorem kg_2581_62 : IPChk.allR (Pts.glueIB K2581.lits KW_2581) 62 16 = true := by decide +kernel

end B334.E1x.Pts.S707
