import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2963L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2963 of `S707`, parts 544 … 638, re-packed by predicted kernel memory (4.33 of 8.19 GB;
stage707_v5; the theorems are v3's `K2963C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2963_544 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2963.lits.getD i 0)) 544 3 = true := by
  decide +kernel
theorem kg_2963_544 : IPChk.allR (Pts.glueIB K2963.lits KW_2963) 544 3 = true := by decide +kernel
theorem kb_2963_547 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2963.lits.getD i 0)) 547 32 = true := by
  decide +kernel
theorem kg_2963_547 : IPChk.allR (Pts.glueIB K2963.lits KW_2963) 547 32 = true := by decide +kernel
theorem kb_2963_579 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2963.lits.getD i 0)) 579 32 = true := by
  decide +kernel
theorem kg_2963_579 : IPChk.allR (Pts.glueIB K2963.lits KW_2963) 579 32 = true := by decide +kernel
theorem kb_2963_611 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2963.lits.getD i 0)) 611 24 = true := by
  decide +kernel
theorem kg_2963_611 : IPChk.allR (Pts.glueIB K2963.lits KW_2963) 611 24 = true := by decide +kernel
theorem kb_2963_635 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2963.lits.getD i 0)) 635 4 = true := by
  decide +kernel
theorem kg_2963_635 : IPChk.allR (Pts.glueIB K2963.lits KW_2963) 635 4 = true := by decide +kernel

end B334.E1x.Pts.S707
