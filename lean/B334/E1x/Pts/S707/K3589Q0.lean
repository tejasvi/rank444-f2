import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3589L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3589 of `S707`, parts 0 … 9, re-packed by predicted kernel memory (1.29 of 8.19 GB;
stage707_v5; the theorems are v3's `K3589C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3589_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3589.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_3589_0 : IPChk.allR (Pts.glueIB K3589.lits KW_3589) 0 9 = true := by decide +kernel
theorem kb_3589_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3589.lits.getD i 0)) 9 1 = true := by
  decide +kernel
theorem kg_3589_9 : IPChk.allR (Pts.glueIB K3589.lits KW_3589) 9 1 = true := by decide +kernel

end B334.E1x.Pts.S707
