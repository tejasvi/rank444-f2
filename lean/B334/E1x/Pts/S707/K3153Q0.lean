import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3153L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3153 of `S707`, parts 0 … 65, re-packed by predicted kernel memory (3.99 of 8.19 GB;
stage707_v5; the theorems are v3's `K3153C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3153_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_3153_0 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 0 9 = true := by decide +kernel
theorem kb_3153_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_3153_9 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 9 2 = true := by decide +kernel
theorem kb_3153_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 11 8 = true := by
  decide +kernel
theorem kg_3153_11 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 11 8 = true := by decide +kernel
theorem kb_3153_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 19 6 = true := by
  decide +kernel
theorem kg_3153_19 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 19 6 = true := by decide +kernel
theorem kb_3153_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 25 12 = true := by
  decide +kernel
theorem kg_3153_25 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 25 12 = true := by decide +kernel
theorem kb_3153_37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3153.lits.getD i 0)) 37 29 = true := by
  decide +kernel
theorem kg_3153_37 : IPChk.allR (Pts.glueIB K3153.lits KW_3153) 37 29 = true := by decide +kernel

end B334.E1x.Pts.S707
