import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2131L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2131 of `S707`, parts 490 … 564, re-packed by predicted kernel memory (4.16 of 8.19 GB;
stage707_v5; the theorems are v3's `K2131C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2131_490 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2131.lits.getD i 0)) 490 4 = true := by
  decide +kernel
theorem kg_2131_490 : IPChk.allR (Pts.glueIB K2131.lits KW_2131) 490 4 = true := by decide +kernel
theorem kb_2131_494 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2131.lits.getD i 0)) 494 29 = true := by
  decide +kernel
theorem kg_2131_494 : IPChk.allR (Pts.glueIB K2131.lits KW_2131) 494 29 = true := by decide +kernel
theorem kb_2131_523 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2131.lits.getD i 0)) 523 29 = true := by
  decide +kernel
theorem kg_2131_523 : IPChk.allR (Pts.glueIB K2131.lits KW_2131) 523 29 = true := by decide +kernel
theorem kb_2131_552 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2131.lits.getD i 0)) 552 8 = true := by
  decide +kernel
theorem kg_2131_552 : IPChk.allR (Pts.glueIB K2131.lits KW_2131) 552 8 = true := by decide +kernel
theorem kb_2131_560 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2131.lits.getD i 0)) 560 5 = true := by
  decide +kernel
theorem kg_2131_560 : IPChk.allR (Pts.glueIB K2131.lits KW_2131) 560 5 = true := by decide +kernel

end B334.E1x.Pts.S707
