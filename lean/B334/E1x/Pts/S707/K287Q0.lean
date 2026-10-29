import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K287L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 287 of `S707`, parts 0 … 71, re-packed by predicted kernel memory (8.02 of 8.19 GB;
stage707_v5; the theorems are v3's `K287C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_287_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_287_0 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1 = true := by decide +kernel
theorem kb_287_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_287_1 : IPChk.allR (Pts.glueIB K287.lits KW_287) 1 1 = true := by decide +kernel
theorem kb_287_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_287_2 : IPChk.allR (Pts.glueIB K287.lits KW_287) 2 2 = true := by decide +kernel
theorem kb_287_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 4 4 = true := by
  decide +kernel
theorem kg_287_4 : IPChk.allR (Pts.glueIB K287.lits KW_287) 4 4 = true := by decide +kernel
theorem kb_287_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 8 25 = true := by
  decide +kernel
theorem kg_287_8 : IPChk.allR (Pts.glueIB K287.lits KW_287) 8 25 = true := by decide +kernel
theorem kb_287_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 33 7 = true := by
  decide +kernel
theorem kg_287_33 : IPChk.allR (Pts.glueIB K287.lits KW_287) 33 7 = true := by decide +kernel
theorem kb_287_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 40 18 = true := by
  decide +kernel
theorem kg_287_40 : IPChk.allR (Pts.glueIB K287.lits KW_287) 40 18 = true := by decide +kernel
theorem kb_287_58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 58 4 = true := by
  decide +kernel
theorem kg_287_58 : IPChk.allR (Pts.glueIB K287.lits KW_287) 58 4 = true := by decide +kernel
theorem kb_287_62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 62 2 = true := by
  decide +kernel
theorem kg_287_62 : IPChk.allR (Pts.glueIB K287.lits KW_287) 62 2 = true := by decide +kernel
theorem kb_287_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 64 8 = true := by
  decide +kernel
theorem kg_287_64 : IPChk.allR (Pts.glueIB K287.lits KW_287) 64 8 = true := by decide +kernel

end B334.E1x.Pts.S707
