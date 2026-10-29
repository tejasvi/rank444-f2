import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4046L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4046 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.28 of 8.19 GB;
stage707_v5; the theorems are v3's `K4046C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4046_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4046.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4046_0 : IPChk.allR (Pts.glueIB K4046.lits KW_4046) 0 2 = true := by decide +kernel
theorem kb_4046_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4046.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_4046_2 : IPChk.allR (Pts.glueIB K4046.lits KW_4046) 2 1 = true := by decide +kernel

end B334.E1x.Pts.S707
