import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7162L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7162 of `S707`, parts 0 … 11, re-packed by predicted kernel memory (2.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K7162C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7162_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_7162_0 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 0 9 = true := by decide +kernel
theorem kb_7162_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_7162_9 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 9 2 = true := by decide +kernel
theorem kb_7162_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 11 1 = true := by
  decide +kernel
theorem kg_7162_11 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 11 1 = true := by decide +kernel

end B334.E1x.Pts.S707
