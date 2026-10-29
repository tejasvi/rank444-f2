import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6370L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6370 of `S707`, parts 0 … 31, re-packed by predicted kernel memory (2.90 of 8.19 GB;
stage707_v5; the theorems are v3's `K6370C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6370_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6370.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6370_0 : IPChk.allR (Pts.glueIB K6370.lits KW_6370) 0 2 = true := by decide +kernel
theorem kb_6370_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6370.lits.getD i 0)) 2 16 = true := by
  decide +kernel
theorem kg_6370_2 : IPChk.allR (Pts.glueIB K6370.lits KW_6370) 2 16 = true := by decide +kernel
theorem kb_6370_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6370.lits.getD i 0)) 18 2 = true := by
  decide +kernel
theorem kg_6370_18 : IPChk.allR (Pts.glueIB K6370.lits KW_6370) 18 2 = true := by decide +kernel
theorem kb_6370_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6370.lits.getD i 0)) 20 12 = true := by
  decide +kernel
theorem kg_6370_20 : IPChk.allR (Pts.glueIB K6370.lits KW_6370) 20 12 = true := by decide +kernel

end B334.E1x.Pts.S707
