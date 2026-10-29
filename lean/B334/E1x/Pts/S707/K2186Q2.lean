import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2186L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2186 of `S707`, parts 216 … 244, re-packed by predicted kernel memory (1.25 of 8.19 GB;
stage707_v5; the theorems are v3's `K2186C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2186_216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2186.lits.getD i 0)) 216 23 = true := by
  decide +kernel
theorem kg_2186_216 : IPChk.allR (Pts.glueIB K2186.lits KW_2186) 216 23 = true := by decide +kernel
theorem kb_2186_239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2186.lits.getD i 0)) 239 6 = true := by
  decide +kernel
theorem kg_2186_239 : IPChk.allR (Pts.glueIB K2186.lits KW_2186) 239 6 = true := by decide +kernel

end B334.E1x.Pts.S707
