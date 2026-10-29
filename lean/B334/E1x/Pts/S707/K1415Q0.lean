import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1415L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1415 of `S707`, parts 0 … 71, re-packed by predicted kernel memory (7.78 of 8.19 GB;
stage707_v5; the theorems are v3's `K1415C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1415_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_1415_0 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 1 = true := by decide +kernel
theorem kb_1415_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_1415_1 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 1 2 = true := by decide +kernel
theorem kb_1415_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 3 13 = true := by
  decide +kernel
theorem kg_1415_3 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 3 13 = true := by decide +kernel
theorem kb_1415_16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 16 18 = true := by
  decide +kernel
theorem kg_1415_16 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 16 18 = true := by decide +kernel
theorem kb_1415_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 34 6 = true := by
  decide +kernel
theorem kg_1415_34 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 34 6 = true := by decide +kernel
theorem kb_1415_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 40 2 = true := by
  decide +kernel
theorem kg_1415_40 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 40 2 = true := by decide +kernel
theorem kb_1415_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 42 22 = true := by
  decide +kernel
theorem kg_1415_42 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 42 22 = true := by decide +kernel
theorem kb_1415_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 64 2 = true := by
  decide +kernel
theorem kg_1415_64 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 64 2 = true := by decide +kernel
theorem kb_1415_66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 66 6 = true := by
  decide +kernel
theorem kg_1415_66 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 66 6 = true := by decide +kernel

end B334.E1x.Pts.S707
