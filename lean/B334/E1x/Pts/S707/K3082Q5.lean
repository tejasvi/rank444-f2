import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3082L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3082 of `S707`, parts 630 … 705, re-packed by predicted kernel memory (3.46 of 8.19 GB;
stage707_v5; the theorems are v3's `K3082C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3082_630 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3082.lits.getD i 0)) 630 27 = true := by
  decide +kernel
theorem kg_3082_630 : IPChk.allR (Pts.glueIB K3082.lits KW_3082) 630 27 = true := by decide +kernel
theorem kb_3082_657 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3082.lits.getD i 0)) 657 7 = true := by
  decide +kernel
theorem kg_3082_657 : IPChk.allR (Pts.glueIB K3082.lits KW_3082) 657 7 = true := by decide +kernel
theorem kb_3082_664 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3082.lits.getD i 0)) 664 7 = true := by
  decide +kernel
theorem kg_3082_664 : IPChk.allR (Pts.glueIB K3082.lits KW_3082) 664 7 = true := by decide +kernel
theorem kb_3082_671 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3082.lits.getD i 0)) 671 31 = true := by
  decide +kernel
theorem kg_3082_671 : IPChk.allR (Pts.glueIB K3082.lits KW_3082) 671 31 = true := by decide +kernel
theorem kb_3082_702 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3082.lits.getD i 0)) 702 4 = true := by
  decide +kernel
theorem kg_3082_702 : IPChk.allR (Pts.glueIB K3082.lits KW_3082) 702 4 = true := by decide +kernel

end B334.E1x.Pts.S707
