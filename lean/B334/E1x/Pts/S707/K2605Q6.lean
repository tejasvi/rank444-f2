import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2605L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2605 of `S707`, parts 751 … 757, re-packed by predicted kernel memory (1.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K2605C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2605_751 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2605.lits.getD i 0)) 751 4 = true := by
  decide +kernel
theorem kg_2605_751 : IPChk.allR (Pts.glueIB K2605.lits KW_2605) 751 4 = true := by decide +kernel
theorem kb_2605_755 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2605.lits.getD i 0)) 755 3 = true := by
  decide +kernel
theorem kg_2605_755 : IPChk.allR (Pts.glueIB K2605.lits KW_2605) 755 3 = true := by decide +kernel

end B334.E1x.Pts.S707
