import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6893L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6893 of `S707`, parts 29 … 31, re-packed by predicted kernel memory (0.96 of 8.19 GB;
stage707_v5; the theorems are v3's `K6893C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6893_29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 29 2 = true := by
  decide +kernel
theorem kg_6893_29 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 29 2 = true := by decide +kernel
theorem kb_6893_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 31 1 = true := by
  decide +kernel
theorem kg_6893_31 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 31 1 = true := by decide +kernel

end B334.E1x.Pts.S707
