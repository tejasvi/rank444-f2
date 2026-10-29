import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1690L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1690 of `S707`, parts 446 … 595, re-packed by predicted kernel memory (3.04 of 8.19 GB;
stage707_v5; the theorems are v3's `K1690C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1690_446 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1690.lits.getD i 0)) 446 27 = true := by
  decide +kernel
theorem kg_1690_446 : IPChk.allR (Pts.glueIB K1690.lits KW_1690) 446 27 = true := by decide +kernel
theorem kb_1690_473 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1690.lits.getD i 0)) 473 55 = true := by
  decide +kernel
theorem kg_1690_473 : IPChk.allR (Pts.glueIB K1690.lits KW_1690) 473 55 = true := by decide +kernel
theorem kb_1690_528 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1690.lits.getD i 0)) 528 30 = true := by
  decide +kernel
theorem kg_1690_528 : IPChk.allR (Pts.glueIB K1690.lits KW_1690) 528 30 = true := by decide +kernel
theorem kb_1690_558 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1690.lits.getD i 0)) 558 38 = true := by
  decide +kernel
theorem kg_1690_558 : IPChk.allR (Pts.glueIB K1690.lits KW_1690) 558 38 = true := by decide +kernel

end B334.E1x.Pts.S707
