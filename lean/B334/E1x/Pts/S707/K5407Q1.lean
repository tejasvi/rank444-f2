import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5407L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5407 of `S707`, parts 144 … 149, re-packed by predicted kernel memory (0.72 of 8.19 GB;
stage707_v5; the theorems are v3's `K5407C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5407_144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5407.lits.getD i 0)) 144 6 = true := by
  decide +kernel
theorem kg_5407_144 : IPChk.allR (Pts.glueIB K5407.lits KW_5407) 144 6 = true := by decide +kernel

end B334.E1x.Pts.S707
