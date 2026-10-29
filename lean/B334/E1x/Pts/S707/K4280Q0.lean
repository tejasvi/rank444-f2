import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4280L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4280 of `S707`, parts 0 … 31, re-packed by predicted kernel memory (6.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K4280C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4280_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_4280_0 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 0 1 = true := by decide +kernel
theorem kb_4280_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 1 5 = true := by
  decide +kernel
theorem kg_4280_1 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 1 5 = true := by decide +kernel
theorem kb_4280_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 6 1 = true := by
  decide +kernel
theorem kg_4280_6 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 6 1 = true := by decide +kernel
theorem kb_4280_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 7 2 = true := by
  decide +kernel
theorem kg_4280_7 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 7 2 = true := by decide +kernel
theorem kb_4280_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_4280_9 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 9 2 = true := by decide +kernel
theorem kb_4280_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 11 6 = true := by
  decide +kernel
theorem kg_4280_11 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 11 6 = true := by decide +kernel
theorem kb_4280_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 17 3 = true := by
  decide +kernel
theorem kg_4280_17 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 17 3 = true := by decide +kernel
theorem kb_4280_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 20 4 = true := by
  decide +kernel
theorem kg_4280_20 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 20 4 = true := by decide +kernel
theorem kb_4280_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4280.lits.getD i 0)) 24 8 = true := by
  decide +kernel
theorem kg_4280_24 : IPChk.allR (Pts.glueIB K4280.lits KW_4280) 24 8 = true := by decide +kernel

end B334.E1x.Pts.S707
