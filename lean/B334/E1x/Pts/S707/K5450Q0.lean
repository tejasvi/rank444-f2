import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5450L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5450 of `S707`, parts 0 … 24, re-packed by predicted kernel memory (2.76 of 8.19 GB;
stage707_v5; the theorems are v3's `K5450C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5450_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5450.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_5450_0 : IPChk.allR (Pts.glueIB K5450.lits KW_5450) 0 5 = true := by decide +kernel
theorem kb_5450_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5450.lits.getD i 0)) 5 8 = true := by
  decide +kernel
theorem kg_5450_5 : IPChk.allR (Pts.glueIB K5450.lits KW_5450) 5 8 = true := by decide +kernel
theorem kb_5450_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5450.lits.getD i 0)) 13 2 = true := by
  decide +kernel
theorem kg_5450_13 : IPChk.allR (Pts.glueIB K5450.lits KW_5450) 13 2 = true := by decide +kernel
theorem kb_5450_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5450.lits.getD i 0)) 15 10 = true := by
  decide +kernel
theorem kg_5450_15 : IPChk.allR (Pts.glueIB K5450.lits KW_5450) 15 10 = true := by decide +kernel

end B334.E1x.Pts.S707
