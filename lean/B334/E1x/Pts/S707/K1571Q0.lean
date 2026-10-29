import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1571L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1571 of `S707`, parts 0 … 33, re-packed by predicted kernel memory (3.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K1571C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1571_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1571.lits.getD i 0)) 0 12 = true := by
  decide +kernel
theorem kg_1571_0 : IPChk.allR (Pts.glueIB K1571.lits KW_1571) 0 12 = true := by decide +kernel
theorem kb_1571_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1571.lits.getD i 0)) 12 11 = true := by
  decide +kernel
theorem kg_1571_12 : IPChk.allR (Pts.glueIB K1571.lits KW_1571) 12 11 = true := by decide +kernel
theorem kb_1571_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1571.lits.getD i 0)) 23 5 = true := by
  decide +kernel
theorem kg_1571_23 : IPChk.allR (Pts.glueIB K1571.lits KW_1571) 23 5 = true := by decide +kernel
theorem kb_1571_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1571.lits.getD i 0)) 28 5 = true := by
  decide +kernel
theorem kg_1571_28 : IPChk.allR (Pts.glueIB K1571.lits KW_1571) 28 5 = true := by decide +kernel
theorem kb_1571_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1571.lits.getD i 0)) 33 1 = true := by
  decide +kernel
theorem kg_1571_33 : IPChk.allR (Pts.glueIB K1571.lits KW_1571) 33 1 = true := by decide +kernel

end B334.E1x.Pts.S707
