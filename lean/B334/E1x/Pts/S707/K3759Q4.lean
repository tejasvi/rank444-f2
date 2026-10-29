import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3759L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3759 of `S707`, parts 467 … 496, re-packed by predicted kernel memory (1.39 of 8.19 GB;
stage707_v5; the theorems are v3's `K3759C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3759_467 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3759.lits.getD i 0)) 467 21 = true := by
  decide +kernel
theorem kg_3759_467 : IPChk.allR (Pts.glueIB K3759.lits KW_3759) 467 21 = true := by decide +kernel
theorem kb_3759_488 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3759.lits.getD i 0)) 488 9 = true := by
  decide +kernel
theorem kg_3759_488 : IPChk.allR (Pts.glueIB K3759.lits KW_3759) 488 9 = true := by decide +kernel

end B334.E1x.Pts.S707
