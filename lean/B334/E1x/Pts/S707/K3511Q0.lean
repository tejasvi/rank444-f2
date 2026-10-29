import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3511L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3511 of `S707`, parts 0 … 24, re-packed by predicted kernel memory (2.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K3511C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3511_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3511.lits.getD i 0)) 0 22 = true := by
  decide +kernel
theorem kg_3511_0 : IPChk.allR (Pts.glueIB K3511.lits KW_3511) 0 22 = true := by decide +kernel
theorem kb_3511_22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3511.lits.getD i 0)) 22 1 = true := by
  decide +kernel
theorem kg_3511_22 : IPChk.allR (Pts.glueIB K3511.lits KW_3511) 22 1 = true := by decide +kernel
theorem kb_3511_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3511.lits.getD i 0)) 23 2 = true := by
  decide +kernel
theorem kg_3511_23 : IPChk.allR (Pts.glueIB K3511.lits KW_3511) 23 2 = true := by decide +kernel

end B334.E1x.Pts.S707
