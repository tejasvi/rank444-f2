import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3533L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3533 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K3533C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3533_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3533.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3533_0 : IPChk.allR (Pts.glueIB K3533.lits KW_3533) 0 1 = true := by decide +kernel
theorem kb_3533_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3533.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_3533_1 : IPChk.allR (Pts.glueIB K3533.lits KW_3533) 1 2 = true := by decide +kernel

end B334.E1x.Pts.S707
