import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5015L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5015 of `S707`, parts 271 … 303, re-packed by predicted kernel memory (1.91 of 8.19 GB;
stage707_v5; the theorems are v3's `K5015C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5015_271 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5015.lits.getD i 0)) 271 26 = true := by
  decide +kernel
theorem kg_5015_271 : IPChk.allR (Pts.glueIB K5015.lits KW_5015) 271 26 = true := by decide +kernel
theorem kb_5015_297 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5015.lits.getD i 0)) 297 5 = true := by
  decide +kernel
theorem kg_5015_297 : IPChk.allR (Pts.glueIB K5015.lits KW_5015) 297 5 = true := by decide +kernel
theorem kb_5015_302 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5015.lits.getD i 0)) 302 2 = true := by
  decide +kernel
theorem kg_5015_302 : IPChk.allR (Pts.glueIB K5015.lits KW_5015) 302 2 = true := by decide +kernel

end B334.E1x.Pts.S707
