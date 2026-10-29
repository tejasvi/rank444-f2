import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2047L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2047 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.26 of 8.19 GB;
stage707_v5; the theorems are v3's `K2047C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2047_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2047.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2047_0 : IPChk.allR (Pts.glueIB K2047.lits KW_2047) 0 2 = true := by decide +kernel
theorem kb_2047_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2047.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_2047_2 : IPChk.allR (Pts.glueIB K2047.lits KW_2047) 2 1 = true := by decide +kernel

end B334.E1x.Pts.S707
