import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5370L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5370 of `S707`, parts 0 … 31, re-packed by predicted kernel memory (1.52 of 8.19 GB;
stage707_v5; the theorems are v3's `K5370C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5370_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5370.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_5370_0 : IPChk.allR (Pts.glueIB K5370.lits KW_5370) 0 7 = true := by decide +kernel
theorem kb_5370_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5370.lits.getD i 0)) 7 25 = true := by
  decide +kernel
theorem kg_5370_7 : IPChk.allR (Pts.glueIB K5370.lits KW_5370) 7 25 = true := by decide +kernel

end B334.E1x.Pts.S707
