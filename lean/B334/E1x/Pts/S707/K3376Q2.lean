import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3376L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3376 of `S707`, parts 313 … 360, re-packed by predicted kernel memory (0.65 of 8.19 GB;
stage707_v5; the theorems are v3's `K3376C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3376_313 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3376.lits.getD i 0)) 313 48 = true := by
  decide +kernel
theorem kg_3376_313 : IPChk.allR (Pts.glueIB K3376.lits KW_3376) 313 48 = true := by decide +kernel

end B334.E1x.Pts.S707
