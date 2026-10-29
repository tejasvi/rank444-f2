import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5004L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5004 of `S707`, parts 94 … 104, re-packed by predicted kernel memory (2.19 of 8.19 GB;
stage707_v5; the theorems are v3's `K5004C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5004_94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5004.lits.getD i 0)) 94 8 = true := by
  decide +kernel
theorem kg_5004_94 : IPChk.allR (Pts.glueIB K5004.lits KW_5004) 94 8 = true := by decide +kernel
theorem kb_5004_102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5004.lits.getD i 0)) 102 2 = true := by
  decide +kernel
theorem kg_5004_102 : IPChk.allR (Pts.glueIB K5004.lits KW_5004) 102 2 = true := by decide +kernel
theorem kb_5004_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5004.lits.getD i 0)) 104 1 = true := by
  decide +kernel
theorem kg_5004_104 : IPChk.allR (Pts.glueIB K5004.lits KW_5004) 104 1 = true := by decide +kernel

end B334.E1x.Pts.S707
