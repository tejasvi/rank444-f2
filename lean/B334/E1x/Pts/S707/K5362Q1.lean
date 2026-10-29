import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5362L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5362 of `S707`, parts 140 … 188, re-packed by predicted kernel memory (1.11 of 8.19 GB;
stage707_v5; the theorems are v3's `K5362C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5362_140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5362.lits.getD i 0)) 140 32 = true := by
  decide +kernel
theorem kg_5362_140 : IPChk.allR (Pts.glueIB K5362.lits KW_5362) 140 32 = true := by decide +kernel
theorem kb_5362_172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5362.lits.getD i 0)) 172 17 = true := by
  decide +kernel
theorem kg_5362_172 : IPChk.allR (Pts.glueIB K5362.lits KW_5362) 172 17 = true := by decide +kernel

end B334.E1x.Pts.S707
