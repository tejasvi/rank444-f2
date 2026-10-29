import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6394L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6394 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.52 of 8.19 GB;
stage707_v5; the theorems are v3's `K6394C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6394_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6394.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_6394_0 : IPChk.allR (Pts.glueIB K6394.lits KW_6394) 0 1 = true := by decide +kernel
theorem kb_6394_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6394.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_6394_1 : IPChk.allR (Pts.glueIB K6394.lits KW_6394) 1 2 = true := by decide +kernel

end B334.E1x.Pts.S707
