import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3077L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3077 of `S707`, parts 1431 … 1437, re-packed by predicted kernel memory (0.59 of 8.19 GB;
stage707_v5; the theorems are v3's `K3077C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3077_1431 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 1431 7 = true := by
  decide +kernel
theorem kg_3077_1431 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 1431 7 = true := by decide +kernel

end B334.E1x.Pts.S707
