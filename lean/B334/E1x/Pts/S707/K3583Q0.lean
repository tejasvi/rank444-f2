import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3583L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3583 of `S707`, parts 0 … 35, re-packed by predicted kernel memory (1.89 of 8.19 GB;
stage707_v5; the theorems are v3's `K3583C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3583_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3583.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_3583_0 : IPChk.allR (Pts.glueIB K3583.lits KW_3583) 0 3 = true := by decide +kernel
theorem kb_3583_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3583.lits.getD i 0)) 3 20 = true := by
  decide +kernel
theorem kg_3583_3 : IPChk.allR (Pts.glueIB K3583.lits KW_3583) 3 20 = true := by decide +kernel
theorem kb_3583_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3583.lits.getD i 0)) 23 13 = true := by
  decide +kernel
theorem kg_3583_23 : IPChk.allR (Pts.glueIB K3583.lits KW_3583) 23 13 = true := by decide +kernel

end B334.E1x.Pts.S707
