import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6331L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6331 of `S707`, parts 156 … 211, re-packed by predicted kernel memory (0.67 of 8.19 GB;
stage707_v5; the theorems are v3's `K6331C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6331_156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6331.lits.getD i 0)) 156 56 = true := by
  decide +kernel
theorem kg_6331_156 : IPChk.allR (Pts.glueIB K6331.lits KW_6331) 156 56 = true := by decide +kernel

end B334.E1x.Pts.S707
