import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1639L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1639 of `S707`, parts 0 … 12, re-packed by predicted kernel memory (2.50 of 8.19 GB;
stage707_v5; the theorems are v3's `K1639C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1639_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1639.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_1639_0 : IPChk.allR (Pts.glueIB K1639.lits KW_1639) 0 2 = true := by decide +kernel
theorem kb_1639_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1639.lits.getD i 0)) 2 4 = true := by
  decide +kernel
theorem kg_1639_2 : IPChk.allR (Pts.glueIB K1639.lits KW_1639) 2 4 = true := by decide +kernel
theorem kb_1639_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1639.lits.getD i 0)) 6 4 = true := by
  decide +kernel
theorem kg_1639_6 : IPChk.allR (Pts.glueIB K1639.lits KW_1639) 6 4 = true := by decide +kernel
theorem kb_1639_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1639.lits.getD i 0)) 10 3 = true := by
  decide +kernel
theorem kg_1639_10 : IPChk.allR (Pts.glueIB K1639.lits KW_1639) 10 3 = true := by decide +kernel

end B334.E1x.Pts.S707
