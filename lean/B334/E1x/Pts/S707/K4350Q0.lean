import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4350L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4350 of `S707`, parts 0 … 48, re-packed by predicted kernel memory (2.45 of 8.19 GB;
stage707_v5; the theorems are v3's `K4350C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4350_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4350.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_4350_0 : IPChk.allR (Pts.glueIB K4350.lits KW_4350) 0 11 = true := by decide +kernel
theorem kb_4350_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4350.lits.getD i 0)) 11 2 = true := by
  decide +kernel
theorem kg_4350_11 : IPChk.allR (Pts.glueIB K4350.lits KW_4350) 11 2 = true := by decide +kernel
theorem kb_4350_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4350.lits.getD i 0)) 13 36 = true := by
  decide +kernel
theorem kg_4350_13 : IPChk.allR (Pts.glueIB K4350.lits KW_4350) 13 36 = true := by decide +kernel

end B334.E1x.Pts.S707
