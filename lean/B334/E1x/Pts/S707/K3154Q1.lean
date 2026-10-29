import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3154L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3154 of `S707`, parts 67 … 108, re-packed by predicted kernel memory (1.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K3154C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3154_67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3154.lits.getD i 0)) 67 16 = true := by
  decide +kernel
theorem kg_3154_67 : IPChk.allR (Pts.glueIB K3154.lits KW_3154) 67 16 = true := by decide +kernel
theorem kb_3154_83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3154.lits.getD i 0)) 83 26 = true := by
  decide +kernel
theorem kg_3154_83 : IPChk.allR (Pts.glueIB K3154.lits KW_3154) 83 26 = true := by decide +kernel

end B334.E1x.Pts.S707
