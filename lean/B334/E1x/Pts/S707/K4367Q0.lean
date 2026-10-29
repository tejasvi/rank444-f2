import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4367L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4367 of `S707`, parts 0 … 26, re-packed by predicted kernel memory (1.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K4367C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4367_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4367.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_4367_0 : IPChk.allR (Pts.glueIB K4367.lits KW_4367) 0 3 = true := by decide +kernel
theorem kb_4367_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4367.lits.getD i 0)) 3 17 = true := by
  decide +kernel
theorem kg_4367_3 : IPChk.allR (Pts.glueIB K4367.lits KW_4367) 3 17 = true := by decide +kernel
theorem kb_4367_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4367.lits.getD i 0)) 20 7 = true := by
  decide +kernel
theorem kg_4367_20 : IPChk.allR (Pts.glueIB K4367.lits KW_4367) 20 7 = true := by decide +kernel

end B334.E1x.Pts.S707
