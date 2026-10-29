import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K974L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 974 of `S707`, parts 0 … 5, re-packed by predicted kernel memory (2.05 of 8.19 GB;
stage707_v5; the theorems are v3's `K974C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_974_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_974_0 : IPChk.allR (Pts.glueIB K974.lits KW_974) 0 4 = true := by decide +kernel
theorem kb_974_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_974_4 : IPChk.allR (Pts.glueIB K974.lits KW_974) 4 1 = true := by decide +kernel
theorem kb_974_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 5 1 = true := by
  decide +kernel
theorem kg_974_5 : IPChk.allR (Pts.glueIB K974.lits KW_974) 5 1 = true := by decide +kernel

end B334.E1x.Pts.S707
