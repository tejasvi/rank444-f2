import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6450L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6450 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (1.39 of 8.19 GB;
stage707_v5; the theorems are v3's `K6450C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6450_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6450.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_6450_0 : IPChk.allR (Pts.glueIB K6450.lits KW_6450) 0 7 = true := by decide +kernel
theorem kb_6450_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6450.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_6450_7 : IPChk.allR (Pts.glueIB K6450.lits KW_6450) 7 1 = true := by decide +kernel

end B334.E1x.Pts.S707
