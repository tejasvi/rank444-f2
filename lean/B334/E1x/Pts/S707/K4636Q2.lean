import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4636L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4636 of `S707`, parts 116 … 118, re-packed by predicted kernel memory (0.42 of 8.19 GB;
stage707_v5; the theorems are v3's `K4636C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4636_116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4636.lits.getD i 0)) 116 3 = true := by
  decide +kernel
theorem kg_4636_116 : IPChk.allR (Pts.glueIB K4636.lits KW_4636) 116 3 = true := by decide +kernel

end B334.E1x.Pts.S707
