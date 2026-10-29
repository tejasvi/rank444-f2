import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1692L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1692 of `S707`, parts 364 … 445, re-packed by predicted kernel memory (2.29 of 8.19 GB;
stage707_v5; the theorems are v3's `K1692C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1692_364 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1692.lits.getD i 0)) 364 27 = true := by
  decide +kernel
theorem kg_1692_364 : IPChk.allR (Pts.glueIB K1692.lits KW_1692) 364 27 = true := by decide +kernel
theorem kb_1692_391 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1692.lits.getD i 0)) 391 16 = true := by
  decide +kernel
theorem kg_1692_391 : IPChk.allR (Pts.glueIB K1692.lits KW_1692) 391 16 = true := by decide +kernel
theorem kb_1692_407 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1692.lits.getD i 0)) 407 32 = true := by
  decide +kernel
theorem kg_1692_407 : IPChk.allR (Pts.glueIB K1692.lits KW_1692) 407 32 = true := by decide +kernel
theorem kb_1692_439 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1692.lits.getD i 0)) 439 7 = true := by
  decide +kernel
theorem kg_1692_439 : IPChk.allR (Pts.glueIB K1692.lits KW_1692) 439 7 = true := by decide +kernel

end B334.E1x.Pts.S707
