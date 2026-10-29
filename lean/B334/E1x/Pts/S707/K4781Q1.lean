import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4781L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4781 of `S707`, parts 147 … 175, re-packed by predicted kernel memory (0.77 of 8.19 GB;
stage707_v5; the theorems are v3's `K4781C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4781_147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4781.lits.getD i 0)) 147 29 = true := by
  decide +kernel
theorem kg_4781_147 : IPChk.allR (Pts.glueIB K4781.lits KW_4781) 147 29 = true := by decide +kernel

end B334.E1x.Pts.S707
