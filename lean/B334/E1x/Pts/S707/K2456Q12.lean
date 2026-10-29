import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2456L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2456 of `S707`, parts 1671 … 1694, re-packed by predicted kernel memory (4.49 of 8.19 GB;
stage707_v5; the theorems are v3's `K2456C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2456_1671 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1671 1 = true := by
  decide +kernel
theorem kg_2456_1671 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1671 1 = true := by decide +kernel
theorem kb_2456_1672 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1672 2 = true := by
  decide +kernel
theorem kg_2456_1672 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1672 2 = true := by decide +kernel
theorem kb_2456_1674 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1674 13 = true := by
  decide +kernel
theorem kg_2456_1674 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1674 13 = true := by decide +kernel
theorem kb_2456_1687 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1687 5 = true := by
  decide +kernel
theorem kg_2456_1687 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1687 5 = true := by decide +kernel
theorem kb_2456_1692 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1692 1 = true := by
  decide +kernel
theorem kg_2456_1692 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1692 1 = true := by decide +kernel
theorem kb_2456_1693 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 1693 2 = true := by
  decide +kernel
theorem kg_2456_1693 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 1693 2 = true := by decide +kernel

end B334.E1x.Pts.S707
