import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6204L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6204 of `S707`, parts 177 … 180, re-packed by predicted kernel memory (0.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K6204C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6204_177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6204.lits.getD i 0)) 177 4 = true := by
  decide +kernel
theorem kg_6204_177 : IPChk.allR (Pts.glueIB K6204.lits KW_6204) 177 4 = true := by decide +kernel

end B334.E1x.Pts.S707
