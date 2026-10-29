import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4780L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4780 of `S707`, parts 49 … 49, re-packed by predicted kernel memory (0.49 of 8.19 GB;
stage707_v5; the theorems are v3's `K4780C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4780_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4780.lits.getD i 0)) 49 1 = true := by
  decide +kernel
theorem kg_4780_49 : IPChk.allR (Pts.glueIB K4780.lits KW_4780) 49 1 = true := by decide +kernel

end B334.E1x.Pts.S707
