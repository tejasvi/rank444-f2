import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4348L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4348 of `S707`, parts 0 … 19, re-packed by predicted kernel memory (0.98 of 8.19 GB;
stage707_v5; the theorems are v3's `K4348C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4348_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4348.lits.getD i 0)) 0 19 = true := by
  decide +kernel
theorem kg_4348_0 : IPChk.allR (Pts.glueIB K4348.lits KW_4348) 0 19 = true := by decide +kernel
theorem kb_4348_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4348.lits.getD i 0)) 19 1 = true := by
  decide +kernel
theorem kg_4348_19 : IPChk.allR (Pts.glueIB K4348.lits KW_4348) 19 1 = true := by decide +kernel

end B334.E1x.Pts.S707
