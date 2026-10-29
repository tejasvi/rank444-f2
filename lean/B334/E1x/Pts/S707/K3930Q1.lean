import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3930L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3930 of `S707`, parts 80 … 139, re-packed by predicted kernel memory (4.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K3930C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3930_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 80 2 = true := by
  decide +kernel
theorem kg_3930_80 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 80 2 = true := by decide +kernel
theorem kb_3930_82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 82 22 = true := by
  decide +kernel
theorem kg_3930_82 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 82 22 = true := by decide +kernel
theorem kb_3930_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 104 1 = true := by
  decide +kernel
theorem kg_3930_104 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 104 1 = true := by decide +kernel
theorem kb_3930_105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 105 2 = true := by
  decide +kernel
theorem kg_3930_105 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 105 2 = true := by decide +kernel
theorem kb_3930_107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 107 4 = true := by
  decide +kernel
theorem kg_3930_107 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 107 4 = true := by decide +kernel
theorem kb_3930_111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3930.lits.getD i 0)) 111 29 = true := by
  decide +kernel
theorem kg_3930_111 : IPChk.allR (Pts.glueIB K3930.lits KW_3930) 111 29 = true := by decide +kernel

end B334.E1x.Pts.S707
