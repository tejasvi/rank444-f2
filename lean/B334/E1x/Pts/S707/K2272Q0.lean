import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2272L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2272 of `S707`, parts 0 … 50, re-packed by predicted kernel memory (2.88 of 8.19 GB;
stage707_v5; the theorems are v3's `K2272C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2272_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2272.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2272_0 : IPChk.allR (Pts.glueIB K2272.lits KW_2272) 0 2 = true := by decide +kernel
theorem kb_2272_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2272.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_2272_2 : IPChk.allR (Pts.glueIB K2272.lits KW_2272) 2 6 = true := by decide +kernel
theorem kb_2272_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2272.lits.getD i 0)) 8 19 = true := by
  decide +kernel
theorem kg_2272_8 : IPChk.allR (Pts.glueIB K2272.lits KW_2272) 8 19 = true := by decide +kernel
theorem kb_2272_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2272.lits.getD i 0)) 27 24 = true := by
  decide +kernel
theorem kg_2272_27 : IPChk.allR (Pts.glueIB K2272.lits KW_2272) 27 24 = true := by decide +kernel

end B334.E1x.Pts.S707
