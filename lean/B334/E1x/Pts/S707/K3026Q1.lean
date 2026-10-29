import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3026L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3026 of `S707`, parts 97 … 218, re-packed by predicted kernel memory (3.30 of 8.19 GB;
stage707_v5; the theorems are v3's `K3026C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3026_97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 97 40 = true := by
  decide +kernel
theorem kg_3026_97 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 97 40 = true := by decide +kernel
theorem kb_3026_137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 137 4 = true := by
  decide +kernel
theorem kg_3026_137 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 137 4 = true := by decide +kernel
theorem kb_3026_141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 141 23 = true := by
  decide +kernel
theorem kg_3026_141 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 141 23 = true := by decide +kernel
theorem kb_3026_164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 164 55 = true := by
  decide +kernel
theorem kg_3026_164 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 164 55 = true := by decide +kernel

end B334.E1x.Pts.S707
