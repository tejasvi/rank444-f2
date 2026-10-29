import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4691L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4691 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.28 of 8.19 GB;
stage707_v5; the theorems are v3's `K4691C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4691_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4691.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4691_0 : IPChk.allR (Pts.glueIB K4691.lits KW_4691) 0 2 = true := by decide +kernel
theorem kb_4691_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4691.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_4691_2 : IPChk.allR (Pts.glueIB K4691.lits KW_4691) 2 1 = true := by decide +kernel

end B334.E1x.Pts.S707
