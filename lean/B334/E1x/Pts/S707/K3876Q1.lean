import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3876L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3876 of `S707`, parts 64 … 78, re-packed by predicted kernel memory (3.77 of 8.19 GB;
stage707_v5; the theorems are v3's `K3876C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3876_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 64 1 = true := by
  decide +kernel
theorem kg_3876_64 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 64 1 = true := by decide +kernel
theorem kb_3876_65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 65 8 = true := by
  decide +kernel
theorem kg_3876_65 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 65 8 = true := by decide +kernel
theorem kb_3876_73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 73 2 = true := by
  decide +kernel
theorem kg_3876_73 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 73 2 = true := by decide +kernel
theorem kb_3876_75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 75 1 = true := by
  decide +kernel
theorem kg_3876_75 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 75 1 = true := by decide +kernel
theorem kb_3876_76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 76 2 = true := by
  decide +kernel
theorem kg_3876_76 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 76 2 = true := by decide +kernel
theorem kb_3876_78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3876.lits.getD i 0)) 78 1 = true := by
  decide +kernel
theorem kg_3876_78 : IPChk.allR (Pts.glueIB K3876.lits KW_3876) 78 1 = true := by decide +kernel

end B334.E1x.Pts.S707
