import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3048L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3048 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (1.59 of 8.19 GB;
stage707_v5; the theorems are v3's `K3048C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3048_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3048_0 : IPChk.allR (Pts.glueIB K3048.lits KW_3048) 0 1 = true := by decide +kernel
theorem kb_3048_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 1 3 = true := by
  decide +kernel
theorem kg_3048_1 : IPChk.allR (Pts.glueIB K3048.lits KW_3048) 1 3 = true := by decide +kernel

end B334.E1x.Pts.S707
