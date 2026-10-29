import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3501L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3501 of `S707`, parts 106 … 150, re-packed by predicted kernel memory (1.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K3501C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3501_106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3501.lits.getD i 0)) 106 31 = true := by
  decide +kernel
theorem kg_3501_106 : IPChk.allR (Pts.glueIB K3501.lits KW_3501) 106 31 = true := by decide +kernel
theorem kb_3501_137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3501.lits.getD i 0)) 137 14 = true := by
  decide +kernel
theorem kg_3501_137 : IPChk.allR (Pts.glueIB K3501.lits KW_3501) 137 14 = true := by decide +kernel

end B334.E1x.Pts.S707
