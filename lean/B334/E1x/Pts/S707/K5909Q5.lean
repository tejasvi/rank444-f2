import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5909L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5909 of `S707`, parts 94 … 101, re-packed by predicted kernel memory (2.93 of 8.19 GB;
stage707_v5; the theorems are v3's `K5909C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5909_94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5909.lits.getD i 0)) 94 2 = true := by
  decide +kernel
theorem kg_5909_94 : IPChk.allR (Pts.glueIB K5909.lits KW_5909) 94 2 = true := by decide +kernel
theorem kb_5909_96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5909.lits.getD i 0)) 96 2 = true := by
  decide +kernel
theorem kg_5909_96 : IPChk.allR (Pts.glueIB K5909.lits KW_5909) 96 2 = true := by decide +kernel
theorem kb_5909_98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5909.lits.getD i 0)) 98 3 = true := by
  decide +kernel
theorem kg_5909_98 : IPChk.allR (Pts.glueIB K5909.lits KW_5909) 98 3 = true := by decide +kernel
theorem kb_5909_101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5909.lits.getD i 0)) 101 1 = true := by
  decide +kernel
theorem kg_5909_101 : IPChk.allR (Pts.glueIB K5909.lits KW_5909) 101 1 = true := by decide +kernel

end B334.E1x.Pts.S707
