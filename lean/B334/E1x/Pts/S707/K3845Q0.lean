import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3845L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3845 of `S707`, parts 0 … 57, re-packed by predicted kernel memory (2.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K3845C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3845_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3845.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3845_0 : IPChk.allR (Pts.glueIB K3845.lits KW_3845) 0 2 = true := by decide +kernel
theorem kb_3845_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3845.lits.getD i 0)) 2 28 = true := by
  decide +kernel
theorem kg_3845_2 : IPChk.allR (Pts.glueIB K3845.lits KW_3845) 2 28 = true := by decide +kernel
theorem kb_3845_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3845.lits.getD i 0)) 30 28 = true := by
  decide +kernel
theorem kg_3845_30 : IPChk.allR (Pts.glueIB K3845.lits KW_3845) 30 28 = true := by decide +kernel

end B334.E1x.Pts.S707
