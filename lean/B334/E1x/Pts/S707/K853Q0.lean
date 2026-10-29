import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K853L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 853 of `S707`, parts 0 … 15, re-packed by predicted kernel memory (1.84 of 8.19 GB;
stage707_v5; the theorems are v3's `K853C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_853_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_853_0 : IPChk.allR (Pts.glueIB K853.lits KW_853) 0 1 = true := by decide +kernel
theorem kb_853_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 1 12 = true := by
  decide +kernel
theorem kg_853_1 : IPChk.allR (Pts.glueIB K853.lits KW_853) 1 12 = true := by decide +kernel
theorem kb_853_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 13 3 = true := by
  decide +kernel
theorem kg_853_13 : IPChk.allR (Pts.glueIB K853.lits KW_853) 13 3 = true := by decide +kernel

end B334.E1x.Pts.S707
