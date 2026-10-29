import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5978L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5978 of `S707`, parts 0 … 16, re-packed by predicted kernel memory (2.74 of 8.19 GB;
stage707_v5; the theorems are v3's `K5978C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5978_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5978.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_5978_0 : IPChk.allR (Pts.glueIB K5978.lits KW_5978) 0 7 = true := by decide +kernel
theorem kb_5978_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5978.lits.getD i 0)) 7 7 = true := by
  decide +kernel
theorem kg_5978_7 : IPChk.allR (Pts.glueIB K5978.lits KW_5978) 7 7 = true := by decide +kernel
theorem kb_5978_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5978.lits.getD i 0)) 14 1 = true := by
  decide +kernel
theorem kg_5978_14 : IPChk.allR (Pts.glueIB K5978.lits KW_5978) 14 1 = true := by decide +kernel
theorem kb_5978_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5978.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_5978_15 : IPChk.allR (Pts.glueIB K5978.lits KW_5978) 15 2 = true := by decide +kernel

end B334.E1x.Pts.S707
