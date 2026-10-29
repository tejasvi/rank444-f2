import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3130L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3130 of `S707`, parts 79 … 83, re-packed by predicted kernel memory (2.44 of 8.19 GB;
stage707_v5; the theorems are v3's `K3130C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3130_79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3130.lits.getD i 0)) 79 2 = true := by
  decide +kernel
theorem kg_3130_79 : IPChk.allR (Pts.glueIB K3130.lits KW_3130) 79 2 = true := by decide +kernel
theorem kb_3130_81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3130.lits.getD i 0)) 81 1 = true := by
  decide +kernel
theorem kg_3130_81 : IPChk.allR (Pts.glueIB K3130.lits KW_3130) 81 1 = true := by decide +kernel
theorem kb_3130_82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3130.lits.getD i 0)) 82 1 = true := by
  decide +kernel
theorem kg_3130_82 : IPChk.allR (Pts.glueIB K3130.lits KW_3130) 82 1 = true := by decide +kernel
theorem kb_3130_83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3130.lits.getD i 0)) 83 1 = true := by
  decide +kernel
theorem kg_3130_83 : IPChk.allR (Pts.glueIB K3130.lits KW_3130) 83 1 = true := by decide +kernel

end B334.E1x.Pts.S707
