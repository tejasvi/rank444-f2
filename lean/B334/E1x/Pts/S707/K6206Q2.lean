import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6206L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6206 of `S707`, parts 214 … 266, re-packed by predicted kernel memory (1.43 of 8.19 GB;
stage707_v5; the theorems are v3's `K6206C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6206_214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6206.lits.getD i 0)) 214 11 = true := by
  decide +kernel
theorem kg_6206_214 : IPChk.allR (Pts.glueIB K6206.lits KW_6206) 214 11 = true := by decide +kernel
theorem kb_6206_225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6206.lits.getD i 0)) 225 42 = true := by
  decide +kernel
theorem kg_6206_225 : IPChk.allR (Pts.glueIB K6206.lits KW_6206) 225 42 = true := by decide +kernel

end B334.E1x.Pts.S707
