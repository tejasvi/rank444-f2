import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2466L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2466 of `S707`, parts 376 … 408, re-packed by predicted kernel memory (1.80 of 8.19 GB;
stage707_v5; the theorems are v3's `K2466C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2466_376 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 376 3 = true := by
  decide +kernel
theorem kg_2466_376 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 376 3 = true := by decide +kernel
theorem kb_2466_379 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 379 30 = true := by
  decide +kernel
theorem kg_2466_379 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 379 30 = true := by decide +kernel

end B334.E1x.Pts.S707
