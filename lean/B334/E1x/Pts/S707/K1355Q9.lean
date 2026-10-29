import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1355L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1355 of `S707`, parts 800 … 906, re-packed by predicted kernel memory (4.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K1355C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1355_800 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 800 24 = true := by
  decide +kernel
theorem kg_1355_800 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 800 24 = true := by decide +kernel
theorem kb_1355_824 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 824 31 = true := by
  decide +kernel
theorem kg_1355_824 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 824 31 = true := by decide +kernel
theorem kb_1355_855 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 855 25 = true := by
  decide +kernel
theorem kg_1355_855 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 855 25 = true := by decide +kernel
theorem kb_1355_880 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 880 8 = true := by
  decide +kernel
theorem kg_1355_880 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 880 8 = true := by decide +kernel
theorem kb_1355_888 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 888 15 = true := by
  decide +kernel
theorem kg_1355_888 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 888 15 = true := by decide +kernel
theorem kb_1355_903 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 903 4 = true := by
  decide +kernel
theorem kg_1355_903 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 903 4 = true := by decide +kernel

end B334.E1x.Pts.S707
