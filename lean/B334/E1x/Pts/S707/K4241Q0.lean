import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4241L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4241 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (1.50 of 8.19 GB;
stage707_v5; the theorems are v3's `K4241C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4241_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4241.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_4241_0 : IPChk.allR (Pts.glueIB K4241.lits KW_4241) 0 3 = true := by decide +kernel
theorem kb_4241_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4241.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_4241_3 : IPChk.allR (Pts.glueIB K4241.lits KW_4241) 3 1 = true := by decide +kernel

end B334.E1x.Pts.S707
