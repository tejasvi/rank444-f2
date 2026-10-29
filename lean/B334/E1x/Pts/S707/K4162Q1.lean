import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4162L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4162 of `S707`, parts 18 … 24, re-packed by predicted kernel memory (2.71 of 8.19 GB;
stage707_v5; the theorems are v3's `K4162C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4162_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4162.lits.getD i 0)) 18 2 = true := by
  decide +kernel
theorem kg_4162_18 : IPChk.allR (Pts.glueIB K4162.lits KW_4162) 18 2 = true := by decide +kernel
theorem kb_4162_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4162.lits.getD i 0)) 20 2 = true := by
  decide +kernel
theorem kg_4162_20 : IPChk.allR (Pts.glueIB K4162.lits KW_4162) 20 2 = true := by decide +kernel
theorem kb_4162_22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4162.lits.getD i 0)) 22 2 = true := by
  decide +kernel
theorem kg_4162_22 : IPChk.allR (Pts.glueIB K4162.lits KW_4162) 22 2 = true := by decide +kernel
theorem kb_4162_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4162.lits.getD i 0)) 24 1 = true := by
  decide +kernel
theorem kg_4162_24 : IPChk.allR (Pts.glueIB K4162.lits KW_4162) 24 1 = true := by decide +kernel

end B334.E1x.Pts.S707
