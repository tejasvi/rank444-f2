import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K751L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 751 of `S707`, parts 0 … 4, re-packed by predicted kernel memory (1.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K751C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_751_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K751.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_751_0 : IPChk.allR (Pts.glueIB K751.lits KW_751) 0 1 = true := by decide +kernel
theorem kb_751_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K751.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_751_1 : IPChk.allR (Pts.glueIB K751.lits KW_751) 1 1 = true := by decide +kernel
theorem kb_751_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K751.lits.getD i 0)) 2 3 = true := by
  decide +kernel
theorem kg_751_2 : IPChk.allR (Pts.glueIB K751.lits KW_751) 2 3 = true := by decide +kernel

end B334.E1x.Pts.S707
