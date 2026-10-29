import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4838L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4838 of `S707`, parts 0 … 36, re-packed by predicted kernel memory (1.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K4838C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4838_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4838.lits.getD i 0)) 0 17 = true := by
  decide +kernel
theorem kg_4838_0 : IPChk.allR (Pts.glueIB K4838.lits KW_4838) 0 17 = true := by decide +kernel
theorem kb_4838_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4838.lits.getD i 0)) 17 20 = true := by
  decide +kernel
theorem kg_4838_17 : IPChk.allR (Pts.glueIB K4838.lits KW_4838) 17 20 = true := by decide +kernel

end B334.E1x.Pts.S707
