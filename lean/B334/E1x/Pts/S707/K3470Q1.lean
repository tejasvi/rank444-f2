import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3470L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3470 of `S707`, parts 150 … 218, re-packed by predicted kernel memory (0.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K3470C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3470_150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3470.lits.getD i 0)) 150 63 = true := by
  decide +kernel
theorem kg_3470_150 : IPChk.allR (Pts.glueIB K3470.lits KW_3470) 150 63 = true := by decide +kernel
theorem kb_3470_213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3470.lits.getD i 0)) 213 6 = true := by
  decide +kernel
theorem kg_3470_213 : IPChk.allR (Pts.glueIB K3470.lits KW_3470) 213 6 = true := by decide +kernel

end B334.E1x.Pts.S707
