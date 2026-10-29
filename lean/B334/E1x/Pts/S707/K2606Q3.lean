import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2606L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2606 of `S707`, parts 550 … 600, re-packed by predicted kernel memory (3.67 of 8.19 GB;
stage707_v5; the theorems are v3's `K2606C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2606_550 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 550 26 = true := by
  decide +kernel
theorem kg_2606_550 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 550 26 = true := by decide +kernel
theorem kb_2606_576 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 576 3 = true := by
  decide +kernel
theorem kg_2606_576 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 576 3 = true := by decide +kernel
theorem kb_2606_579 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 579 6 = true := by
  decide +kernel
theorem kg_2606_579 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 579 6 = true := by decide +kernel
theorem kb_2606_585 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 585 4 = true := by
  decide +kernel
theorem kg_2606_585 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 585 4 = true := by decide +kernel
theorem kb_2606_589 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 589 10 = true := by
  decide +kernel
theorem kg_2606_589 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 589 10 = true := by decide +kernel
theorem kb_2606_599 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2606.lits.getD i 0)) 599 2 = true := by
  decide +kernel
theorem kg_2606_599 : IPChk.allR (Pts.glueIB K2606.lits KW_2606) 599 2 = true := by decide +kernel

end B334.E1x.Pts.S707
