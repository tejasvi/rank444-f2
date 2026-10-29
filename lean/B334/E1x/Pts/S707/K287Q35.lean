import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K287L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 287 of `S707`, parts 5148 … 5150, re-packed by predicted kernel memory (0.42 of 8.19 GB;
stage707_v5; the theorems are v3's `K287C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_287_5148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 5148 3 = true := by
  decide +kernel
theorem kg_287_5148 : IPChk.allR (Pts.glueIB K287.lits KW_287) 5148 3 = true := by decide +kernel

end B334.E1x.Pts.S707
