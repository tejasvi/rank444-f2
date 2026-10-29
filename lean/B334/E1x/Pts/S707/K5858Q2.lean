import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5858L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5858 of `S707`, parts 28 … 30, re-packed by predicted kernel memory (0.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K5858C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5858_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5858.lits.getD i 0)) 28 3 = true := by
  decide +kernel
theorem kg_5858_28 : IPChk.allR (Pts.glueIB K5858.lits KW_5858) 28 3 = true := by decide +kernel

end B334.E1x.Pts.S707
