import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7004L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7004 of `S707`, parts 449 … 491, re-packed by predicted kernel memory (1.95 of 8.19 GB;
stage707_v5; the theorems are v3's `K7004C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7004_449 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 449 11 = true := by
  decide +kernel
theorem kg_7004_449 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 449 11 = true := by decide +kernel
theorem kb_7004_460 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 460 12 = true := by
  decide +kernel
theorem kg_7004_460 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 460 12 = true := by decide +kernel
theorem kb_7004_472 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 472 20 = true := by
  decide +kernel
theorem kg_7004_472 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 472 20 = true := by decide +kernel

end B334.E1x.Pts.S707
