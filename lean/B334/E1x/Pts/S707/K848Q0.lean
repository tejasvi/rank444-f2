import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K848L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 848 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (0.98 of 8.19 GB;
stage707_v5; the theorems are v3's `K848C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_848_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_848_0 : IPChk.allR (Pts.glueIB K848.lits KW_848) 0 3 = true := by decide +kernel
theorem kb_848_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_848_3 : IPChk.allR (Pts.glueIB K848.lits KW_848) 3 1 = true := by decide +kernel

end B334.E1x.Pts.S707
