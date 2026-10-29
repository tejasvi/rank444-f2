import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6057L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6057 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (1.34 of 8.19 GB;
stage707_v5; the theorems are v3's `K6057C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6057_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6057.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6057_0 : IPChk.allR (Pts.glueIB K6057.lits KW_6057) 0 2 = true := by decide +kernel
theorem kb_6057_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6057.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_6057_2 : IPChk.allR (Pts.glueIB K6057.lits KW_6057) 2 6 = true := by decide +kernel

end B334.E1x.Pts.S707
