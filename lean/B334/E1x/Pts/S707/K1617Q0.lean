import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1617L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1617 of `S707`, parts 0 … 12, re-packed by predicted kernel memory (1.94 of 8.19 GB;
stage707_v5; the theorems are v3's `K1617C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1617_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1617.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_1617_0 : IPChk.allR (Pts.glueIB K1617.lits KW_1617) 0 9 = true := by decide +kernel
theorem kb_1617_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1617.lits.getD i 0)) 9 3 = true := by
  decide +kernel
theorem kg_1617_9 : IPChk.allR (Pts.glueIB K1617.lits KW_1617) 9 3 = true := by decide +kernel
theorem kb_1617_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1617.lits.getD i 0)) 12 1 = true := by
  decide +kernel
theorem kg_1617_12 : IPChk.allR (Pts.glueIB K1617.lits KW_1617) 12 1 = true := by decide +kernel

end B334.E1x.Pts.S707
