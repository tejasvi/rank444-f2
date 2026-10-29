import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4709L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4709 of `S707`, parts 0 … 47, re-packed by predicted kernel memory (5.15 of 8.19 GB;
stage707_v5; the theorems are v3's `K4709C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4709_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4709_0 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 0 2 = true := by decide +kernel
theorem kb_4709_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_4709_2 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 2 6 = true := by decide +kernel
theorem kb_4709_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 8 2 = true := by
  decide +kernel
theorem kg_4709_8 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 8 2 = true := by decide +kernel
theorem kb_4709_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 10 16 = true := by
  decide +kernel
theorem kg_4709_10 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 10 16 = true := by decide +kernel
theorem kb_4709_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 26 1 = true := by
  decide +kernel
theorem kg_4709_26 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 26 1 = true := by decide +kernel
theorem kb_4709_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 27 20 = true := by
  decide +kernel
theorem kg_4709_27 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 27 20 = true := by decide +kernel
theorem kb_4709_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4709.lits.getD i 0)) 47 1 = true := by
  decide +kernel
theorem kg_4709_47 : IPChk.allR (Pts.glueIB K4709.lits KW_4709) 47 1 = true := by decide +kernel

end B334.E1x.Pts.S707
