import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3613L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3613 of `S707`, parts 0 … 5, re-packed by predicted kernel memory (2.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K3613C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3613_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3613.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3613_0 : IPChk.allR (Pts.glueIB K3613.lits KW_3613) 0 1 = true := by decide +kernel
theorem kb_3613_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3613.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_3613_1 : IPChk.allR (Pts.glueIB K3613.lits KW_3613) 1 1 = true := by decide +kernel
theorem kb_3613_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3613.lits.getD i 0)) 2 4 = true := by
  decide +kernel
theorem kg_3613_2 : IPChk.allR (Pts.glueIB K3613.lits KW_3613) 2 4 = true := by decide +kernel

end B334.E1x.Pts.S707
