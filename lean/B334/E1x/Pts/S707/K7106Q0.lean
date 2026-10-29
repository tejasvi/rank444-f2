import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7106L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7106 of `S707`, parts 0 … 1, re-packed by predicted kernel memory (1.20 of 8.19 GB;
stage707_v5; the theorems are v3's `K7106C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7106_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_7106_0 : IPChk.allR (Pts.glueIB K7106.lits KW_7106) 0 1 = true := by decide +kernel
theorem kb_7106_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_7106_1 : IPChk.allR (Pts.glueIB K7106.lits KW_7106) 1 1 = true := by decide +kernel

end B334.E1x.Pts.S707
