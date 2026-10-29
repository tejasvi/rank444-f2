import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4789L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4789 of `S707`, parts 0 … 32, re-packed by predicted kernel memory (1.92 of 8.19 GB;
stage707_v5; the theorems are v3's `K4789C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4789_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4789.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4789_0 : IPChk.allR (Pts.glueIB K4789.lits KW_4789) 0 2 = true := by decide +kernel
theorem kb_4789_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4789.lits.getD i 0)) 2 11 = true := by
  decide +kernel
theorem kg_4789_2 : IPChk.allR (Pts.glueIB K4789.lits KW_4789) 2 11 = true := by decide +kernel
theorem kb_4789_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4789.lits.getD i 0)) 13 20 = true := by
  decide +kernel
theorem kg_4789_13 : IPChk.allR (Pts.glueIB K4789.lits KW_4789) 13 20 = true := by decide +kernel

end B334.E1x.Pts.S707
