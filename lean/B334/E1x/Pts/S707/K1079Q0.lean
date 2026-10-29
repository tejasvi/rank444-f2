import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1079L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1079 of `S707`, parts 0 … 55, re-packed by predicted kernel memory (3.83 of 8.19 GB;
stage707_v5; the theorems are v3's `K1079C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1079_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 10 = true := by
  decide +kernel
theorem kg_1079_0 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 10 = true := by decide +kernel
theorem kb_1079_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 10 17 = true := by
  decide +kernel
theorem kg_1079_10 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 10 17 = true := by decide +kernel
theorem kb_1079_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 27 7 = true := by
  decide +kernel
theorem kg_1079_27 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 27 7 = true := by decide +kernel
theorem kb_1079_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 34 7 = true := by
  decide +kernel
theorem kg_1079_34 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 34 7 = true := by decide +kernel
theorem kb_1079_41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 41 15 = true := by
  decide +kernel
theorem kg_1079_41 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 41 15 = true := by decide +kernel

end B334.E1x.Pts.S707
