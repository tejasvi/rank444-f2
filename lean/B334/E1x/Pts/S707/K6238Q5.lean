import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6238L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6238 of `S707`, parts 454 … 496, re-packed by predicted kernel memory (3.05 of 8.19 GB;
stage707_v5; the theorems are v3's `K6238C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6238_454 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6238.lits.getD i 0)) 454 4 = true := by
  decide +kernel
theorem kg_6238_454 : IPChk.allR (Pts.glueIB K6238.lits KW_6238) 454 4 = true := by decide +kernel
theorem kb_6238_458 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6238.lits.getD i 0)) 458 9 = true := by
  decide +kernel
theorem kg_6238_458 : IPChk.allR (Pts.glueIB K6238.lits KW_6238) 458 9 = true := by decide +kernel
theorem kb_6238_467 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6238.lits.getD i 0)) 467 16 = true := by
  decide +kernel
theorem kg_6238_467 : IPChk.allR (Pts.glueIB K6238.lits KW_6238) 467 16 = true := by decide +kernel
theorem kb_6238_483 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6238.lits.getD i 0)) 483 14 = true := by
  decide +kernel
theorem kg_6238_483 : IPChk.allR (Pts.glueIB K6238.lits KW_6238) 483 14 = true := by decide +kernel

end B334.E1x.Pts.S707
