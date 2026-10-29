import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3407L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3407 of `S707`, parts 155 … 268, re-packed by predicted kernel memory (2.48 of 8.19 GB;
stage707_v5; the theorems are v3's `K3407C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3407_155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3407.lits.getD i 0)) 155 80 = true := by
  decide +kernel
theorem kg_3407_155 : IPChk.allR (Pts.glueIB K3407.lits KW_3407) 155 80 = true := by decide +kernel
theorem kb_3407_235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3407.lits.getD i 0)) 235 2 = true := by
  decide +kernel
theorem kg_3407_235 : IPChk.allR (Pts.glueIB K3407.lits KW_3407) 235 2 = true := by decide +kernel
theorem kb_3407_237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3407.lits.getD i 0)) 237 28 = true := by
  decide +kernel
theorem kg_3407_237 : IPChk.allR (Pts.glueIB K3407.lits KW_3407) 237 28 = true := by decide +kernel
theorem kb_3407_265 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3407.lits.getD i 0)) 265 4 = true := by
  decide +kernel
theorem kg_3407_265 : IPChk.allR (Pts.glueIB K3407.lits KW_3407) 265 4 = true := by decide +kernel

end B334.E1x.Pts.S707
