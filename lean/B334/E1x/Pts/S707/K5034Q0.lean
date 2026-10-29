import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5034L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5034 of `S707`, parts 0 … 5, re-packed by predicted kernel memory (2.42 of 8.19 GB;
stage707_v5; the theorems are v3's `K5034C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5034_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5034.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_5034_0 : IPChk.allR (Pts.glueIB K5034.lits KW_5034) 0 2 = true := by decide +kernel
theorem kb_5034_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5034.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_5034_2 : IPChk.allR (Pts.glueIB K5034.lits KW_5034) 2 2 = true := by decide +kernel
theorem kb_5034_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5034.lits.getD i 0)) 4 2 = true := by
  decide +kernel
theorem kg_5034_4 : IPChk.allR (Pts.glueIB K5034.lits KW_5034) 4 2 = true := by decide +kernel

end B334.E1x.Pts.S707
