import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K300L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 300 of `S707`, parts 634 … 851, re-packed by predicted kernel memory (3.89 of 8.19 GB;
stage707_v5; the theorems are v3's `K300C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_300_634 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 634 90 = true := by
  decide +kernel
theorem kg_300_634 : IPChk.allR (Pts.glueIB K300.lits KW_300) 634 90 = true := by decide +kernel
theorem kb_300_724 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 724 30 = true := by
  decide +kernel
theorem kg_300_724 : IPChk.allR (Pts.glueIB K300.lits KW_300) 724 30 = true := by decide +kernel
theorem kb_300_754 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 754 63 = true := by
  decide +kernel
theorem kg_300_754 : IPChk.allR (Pts.glueIB K300.lits KW_300) 754 63 = true := by decide +kernel
theorem kb_300_817 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 817 17 = true := by
  decide +kernel
theorem kg_300_817 : IPChk.allR (Pts.glueIB K300.lits KW_300) 817 17 = true := by decide +kernel
theorem kb_300_834 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 834 18 = true := by
  decide +kernel
theorem kg_300_834 : IPChk.allR (Pts.glueIB K300.lits KW_300) 834 18 = true := by decide +kernel

end B334.E1x.Pts.S707
