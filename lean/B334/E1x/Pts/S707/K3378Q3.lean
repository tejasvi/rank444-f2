import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3378L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3378 of `S707`, parts 442 … 478, re-packed by predicted kernel memory (0.95 of 8.19 GB;
stage707_v5; the theorems are v3's `K3378C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3378_442 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3378.lits.getD i 0)) 442 31 = true := by
  decide +kernel
theorem kg_3378_442 : IPChk.allR (Pts.glueIB K3378.lits KW_3378) 442 31 = true := by decide +kernel
theorem kb_3378_473 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3378.lits.getD i 0)) 473 6 = true := by
  decide +kernel
theorem kg_3378_473 : IPChk.allR (Pts.glueIB K3378.lits KW_3378) 473 6 = true := by decide +kernel

end B334.E1x.Pts.S707
