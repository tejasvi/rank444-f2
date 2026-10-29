import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3251L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3251 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (2.07 of 8.19 GB;
stage707_v5; the theorems are v3's `K3251C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3251_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3251.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3251_0 : IPChk.allR (Pts.glueIB K3251.lits KW_3251) 0 1 = true := by decide +kernel
theorem kb_3251_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3251.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_3251_1 : IPChk.allR (Pts.glueIB K3251.lits KW_3251) 1 2 = true := by decide +kernel
theorem kb_3251_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3251.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_3251_3 : IPChk.allR (Pts.glueIB K3251.lits KW_3251) 3 1 = true := by decide +kernel

end B334.E1x.Pts.S707
