import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4645L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4645 of `S707`, parts 0 … 121, re-packed by predicted kernel memory (3.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K4645C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4645_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4645.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4645_0 : IPChk.allR (Pts.glueIB K4645.lits KW_4645) 0 2 = true := by decide +kernel
theorem kb_4645_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4645.lits.getD i 0)) 2 11 = true := by
  decide +kernel
theorem kg_4645_2 : IPChk.allR (Pts.glueIB K4645.lits KW_4645) 2 11 = true := by decide +kernel
theorem kb_4645_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4645.lits.getD i 0)) 13 82 = true := by
  decide +kernel
theorem kg_4645_13 : IPChk.allR (Pts.glueIB K4645.lits KW_4645) 13 82 = true := by decide +kernel
theorem kb_4645_95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4645.lits.getD i 0)) 95 27 = true := by
  decide +kernel
theorem kg_4645_95 : IPChk.allR (Pts.glueIB K4645.lits KW_4645) 95 27 = true := by decide +kernel

end B334.E1x.Pts.S707
