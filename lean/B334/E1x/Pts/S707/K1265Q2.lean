import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1265L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1265 of `S707`, parts 116 … 121, re-packed by predicted kernel memory (1.89 of 8.19 GB;
stage707_v5; the theorems are v3's `K1265C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1265_116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 116 2 = true := by
  decide +kernel
theorem kg_1265_116 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 116 2 = true := by decide +kernel
theorem kb_1265_118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 118 3 = true := by
  decide +kernel
theorem kg_1265_118 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 118 3 = true := by decide +kernel
theorem kb_1265_121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 121 1 = true := by
  decide +kernel
theorem kg_1265_121 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 121 1 = true := by decide +kernel

end B334.E1x.Pts.S707
