import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2450L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2450 of `S707`, parts 534 … 546, re-packed by predicted kernel memory (4.90 of 8.19 GB;
stage707_v5; the theorems are v3's `K2450C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2450_534 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 534 1 = true := by
  decide +kernel
theorem kg_2450_534 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 534 1 = true := by decide +kernel
theorem kb_2450_535 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 535 3 = true := by
  decide +kernel
theorem kg_2450_535 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 535 3 = true := by decide +kernel
theorem kb_2450_538 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 538 2 = true := by
  decide +kernel
theorem kg_2450_538 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 538 2 = true := by decide +kernel
theorem kb_2450_540 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 540 2 = true := by
  decide +kernel
theorem kg_2450_540 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 540 2 = true := by decide +kernel
theorem kb_2450_542 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 542 2 = true := by
  decide +kernel
theorem kg_2450_542 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 542 2 = true := by decide +kernel
theorem kb_2450_544 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 544 2 = true := by
  decide +kernel
theorem kg_2450_544 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 544 2 = true := by decide +kernel
theorem kb_2450_546 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2450.lits.getD i 0)) 546 1 = true := by
  decide +kernel
theorem kg_2450_546 : IPChk.allR (Pts.glueIB K2450.lits KW_2450) 546 1 = true := by decide +kernel

end B334.E1x.Pts.S707
