import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4550L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4550 of `S707`, parts 48 … 56, re-packed by predicted kernel memory (0.48 of 8.19 GB;
stage707_v5; the theorems are v3's `K4550C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4550_48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4550.lits.getD i 0)) 48 9 = true := by
  decide +kernel
theorem kg_4550_48 : IPChk.allR (Pts.glueIB K4550.lits KW_4550) 48 9 = true := by decide +kernel

end B334.E1x.Pts.S707
