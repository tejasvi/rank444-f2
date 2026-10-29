import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3758L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3758 of `S707`, parts 720 … 742, re-packed by predicted kernel memory (4.16 of 8.19 GB;
stage707_v5; the theorems are v3's `K3758C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3758_720 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3758.lits.getD i 0)) 720 1 = true := by
  decide +kernel
theorem kg_3758_720 : IPChk.allR (Pts.glueIB K3758.lits KW_3758) 720 1 = true := by decide +kernel
theorem kb_3758_721 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3758.lits.getD i 0)) 721 7 = true := by
  decide +kernel
theorem kg_3758_721 : IPChk.allR (Pts.glueIB K3758.lits KW_3758) 721 7 = true := by decide +kernel
theorem kb_3758_728 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3758.lits.getD i 0)) 728 10 = true := by
  decide +kernel
theorem kg_3758_728 : IPChk.allR (Pts.glueIB K3758.lits KW_3758) 728 10 = true := by decide +kernel
theorem kb_3758_738 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3758.lits.getD i 0)) 738 3 = true := by
  decide +kernel
theorem kg_3758_738 : IPChk.allR (Pts.glueIB K3758.lits KW_3758) 738 3 = true := by decide +kernel
theorem kb_3758_741 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3758.lits.getD i 0)) 741 2 = true := by
  decide +kernel
theorem kg_3758_741 : IPChk.allR (Pts.glueIB K3758.lits KW_3758) 741 2 = true := by decide +kernel

end B334.E1x.Pts.S707
