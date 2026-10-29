import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K934L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 934 of `S707`, parts 0 … 9, re-packed by predicted kernel memory (3.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K934C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_934_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_934_0 : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 2 = true := by decide +kernel
theorem kb_934_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_934_2 : IPChk.allR (Pts.glueIB K934.lits KW_934) 2 2 = true := by decide +kernel
theorem kb_934_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 4 4 = true := by
  decide +kernel
theorem kg_934_4 : IPChk.allR (Pts.glueIB K934.lits KW_934) 4 4 = true := by decide +kernel
theorem kb_934_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 8 2 = true := by
  decide +kernel
theorem kg_934_8 : IPChk.allR (Pts.glueIB K934.lits KW_934) 8 2 = true := by decide +kernel

end B334.E1x.Pts.S707
