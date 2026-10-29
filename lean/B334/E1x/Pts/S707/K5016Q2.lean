import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5016L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5016 of `S707`, parts 140 … 146, re-packed by predicted kernel memory (1.41 of 8.19 GB;
stage707_v5; the theorems are v3's `K5016C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5016_140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5016.lits.getD i 0)) 140 2 = true := by
  decide +kernel
theorem kg_5016_140 : IPChk.allR (Pts.glueIB K5016.lits KW_5016) 140 2 = true := by decide +kernel
theorem kb_5016_142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5016.lits.getD i 0)) 142 5 = true := by
  decide +kernel
theorem kg_5016_142 : IPChk.allR (Pts.glueIB K5016.lits KW_5016) 142 5 = true := by decide +kernel

end B334.E1x.Pts.S707
