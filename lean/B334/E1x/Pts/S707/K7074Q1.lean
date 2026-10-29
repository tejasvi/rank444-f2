import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7074L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7074 of `S707`, parts 91 … 109, re-packed by predicted kernel memory (0.87 of 8.19 GB;
stage707_v5; the theorems are v3's `K7074C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7074_91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 91 18 = true := by
  decide +kernel
theorem kg_7074_91 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 91 18 = true := by decide +kernel
theorem kb_7074_109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 109 1 = true := by
  decide +kernel
theorem kg_7074_109 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 109 1 = true := by decide +kernel

end B334.E1x.Pts.S707
