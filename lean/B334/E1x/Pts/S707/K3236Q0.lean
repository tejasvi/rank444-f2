import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3236L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3236 of `S707`, parts 0 … 8, re-packed by predicted kernel memory (2.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K3236C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3236_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3236.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_3236_0 : IPChk.allR (Pts.glueIB K3236.lits KW_3236) 0 7 = true := by decide +kernel
theorem kb_3236_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3236.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_3236_7 : IPChk.allR (Pts.glueIB K3236.lits KW_3236) 7 1 = true := by decide +kernel
theorem kb_3236_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3236.lits.getD i 0)) 8 1 = true := by
  decide +kernel
theorem kg_3236_8 : IPChk.allR (Pts.glueIB K3236.lits KW_3236) 8 1 = true := by decide +kernel

end B334.E1x.Pts.S707
