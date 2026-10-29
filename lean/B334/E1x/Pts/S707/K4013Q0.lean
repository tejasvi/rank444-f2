import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4013L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4013 of `S707`, parts 0 … 30, re-packed by predicted kernel memory (1.57 of 8.19 GB;
stage707_v5; the theorems are v3's `K4013C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4013_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4013.lits.getD i 0)) 0 12 = true := by
  decide +kernel
theorem kg_4013_0 : IPChk.allR (Pts.glueIB K4013.lits KW_4013) 0 12 = true := by decide +kernel
theorem kb_4013_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4013.lits.getD i 0)) 12 19 = true := by
  decide +kernel
theorem kg_4013_12 : IPChk.allR (Pts.glueIB K4013.lits KW_4013) 12 19 = true := by decide +kernel

end B334.E1x.Pts.S707
