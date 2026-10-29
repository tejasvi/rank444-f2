import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2470L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2470 of `S707`, parts 247 … 260, re-packed by predicted kernel memory (0.65 of 8.19 GB;
stage707_v5; the theorems are v3's `K2470C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2470_247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 247 14 = true := by
  decide +kernel
theorem kg_2470_247 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 247 14 = true := by decide +kernel

end B334.E1x.Pts.S707
