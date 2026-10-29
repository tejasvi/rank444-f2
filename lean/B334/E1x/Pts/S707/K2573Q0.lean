import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2573L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2573 of `S707`, parts 0 … 96, re-packed by predicted kernel memory (2.97 of 8.19 GB;
stage707_v5; the theorems are v3's `K2573C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2573_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2573.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2573_0 : IPChk.allR (Pts.glueIB K2573.lits KW_2573) 0 1 = true := by decide +kernel
theorem kb_2573_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2573.lits.getD i 0)) 1 10 = true := by
  decide +kernel
theorem kg_2573_1 : IPChk.allR (Pts.glueIB K2573.lits KW_2573) 1 10 = true := by decide +kernel
theorem kb_2573_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2573.lits.getD i 0)) 11 56 = true := by
  decide +kernel
theorem kg_2573_11 : IPChk.allR (Pts.glueIB K2573.lits KW_2573) 11 56 = true := by decide +kernel
theorem kb_2573_67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2573.lits.getD i 0)) 67 30 = true := by
  decide +kernel
theorem kg_2573_67 : IPChk.allR (Pts.glueIB K2573.lits KW_2573) 67 30 = true := by decide +kernel

end B334.E1x.Pts.S707
