import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5378L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5378 of `S707`, parts 0 … 4, re-packed by predicted kernel memory (1.91 of 8.19 GB;
stage707_v5; the theorems are v3's `K5378C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5378_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5378.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_5378_0 : IPChk.allR (Pts.glueIB K5378.lits KW_5378) 0 2 = true := by decide +kernel
theorem kb_5378_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5378.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_5378_2 : IPChk.allR (Pts.glueIB K5378.lits KW_5378) 2 2 = true := by decide +kernel
theorem kb_5378_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5378.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_5378_4 : IPChk.allR (Pts.glueIB K5378.lits KW_5378) 4 1 = true := by decide +kernel

end B334.E1x.Pts.S707
