import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5550L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5550 of `S707`, parts 0 … 39, re-packed by predicted kernel memory (1.40 of 8.19 GB;
stage707_v5; the theorems are v3's `K5550C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5550_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5550.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_5550_0 : IPChk.allR (Pts.glueIB K5550.lits KW_5550) 0 4 = true := by decide +kernel
theorem kb_5550_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5550.lits.getD i 0)) 4 36 = true := by
  decide +kernel
theorem kg_5550_4 : IPChk.allR (Pts.glueIB K5550.lits KW_5550) 4 36 = true := by decide +kernel

end B334.E1x.Pts.S707
