import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5026L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5026 of `S707`, parts 72 … 80, re-packed by predicted kernel memory (2.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K5026C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5026_72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5026.lits.getD i 0)) 72 2 = true := by
  decide +kernel
theorem kg_5026_72 : IPChk.allR (Pts.glueIB K5026.lits KW_5026) 72 2 = true := by decide +kernel
theorem kb_5026_74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5026.lits.getD i 0)) 74 3 = true := by
  decide +kernel
theorem kg_5026_74 : IPChk.allR (Pts.glueIB K5026.lits KW_5026) 74 3 = true := by decide +kernel
theorem kb_5026_77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5026.lits.getD i 0)) 77 3 = true := by
  decide +kernel
theorem kg_5026_77 : IPChk.allR (Pts.glueIB K5026.lits KW_5026) 77 3 = true := by decide +kernel
theorem kb_5026_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5026.lits.getD i 0)) 80 1 = true := by
  decide +kernel
theorem kg_5026_80 : IPChk.allR (Pts.glueIB K5026.lits KW_5026) 80 1 = true := by decide +kernel

end B334.E1x.Pts.S707
