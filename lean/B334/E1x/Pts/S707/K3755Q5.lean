import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3755L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3755 of `S707`, parts 718 … 728, re-packed by predicted kernel memory (1.69 of 8.19 GB;
stage707_v5; the theorems are v3's `K3755C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3755_718 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3755.lits.getD i 0)) 718 6 = true := by
  decide +kernel
theorem kg_3755_718 : IPChk.allR (Pts.glueIB K3755.lits KW_3755) 718 6 = true := by decide +kernel
theorem kb_3755_724 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3755.lits.getD i 0)) 724 5 = true := by
  decide +kernel
theorem kg_3755_724 : IPChk.allR (Pts.glueIB K3755.lits KW_3755) 724 5 = true := by decide +kernel

end B334.E1x.Pts.S707
