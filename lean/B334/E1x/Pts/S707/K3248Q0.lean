import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3248L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3248 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (3.47 of 8.19 GB;
stage707_v5; the theorems are v3's `K3248C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3248_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3248.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3248_0 : IPChk.allR (Pts.glueIB K3248.lits KW_3248) 0 1 = true := by decide +kernel
theorem kb_3248_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3248.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_3248_1 : IPChk.allR (Pts.glueIB K3248.lits KW_3248) 1 2 = true := by decide +kernel
theorem kb_3248_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3248.lits.getD i 0)) 3 2 = true := by
  decide +kernel
theorem kg_3248_3 : IPChk.allR (Pts.glueIB K3248.lits KW_3248) 3 2 = true := by decide +kernel
theorem kb_3248_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3248.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_3248_5 : IPChk.allR (Pts.glueIB K3248.lits KW_3248) 5 2 = true := by decide +kernel
theorem kb_3248_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3248.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_3248_7 : IPChk.allR (Pts.glueIB K3248.lits KW_3248) 7 1 = true := by decide +kernel

end B334.E1x.Pts.S707
