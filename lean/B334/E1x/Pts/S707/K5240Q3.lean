import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5240L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5240 of `S707`, parts 228 … 240, re-packed by predicted kernel memory (1.73 of 8.19 GB;
stage707_v5; the theorems are v3's `K5240C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5240_228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5240.lits.getD i 0)) 228 3 = true := by
  decide +kernel
theorem kg_5240_228 : IPChk.allR (Pts.glueIB K5240.lits KW_5240) 228 3 = true := by decide +kernel
theorem kb_5240_231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5240.lits.getD i 0)) 231 10 = true := by
  decide +kernel
theorem kg_5240_231 : IPChk.allR (Pts.glueIB K5240.lits KW_5240) 231 10 = true := by decide +kernel

end B334.E1x.Pts.S707
