import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2480L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2480 of `S707`, parts 0 … 71, re-packed by predicted kernel memory (5.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K2480C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2480_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2480_0 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 2 = true := by decide +kernel
theorem kb_2480_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_2480_2 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 2 6 = true := by decide +kernel
theorem kb_2480_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 8 3 = true := by
  decide +kernel
theorem kg_2480_8 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 8 3 = true := by decide +kernel
theorem kb_2480_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 11 19 = true := by
  decide +kernel
theorem kg_2480_11 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 11 19 = true := by decide +kernel
theorem kb_2480_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 30 14 = true := by
  decide +kernel
theorem kg_2480_30 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 30 14 = true := by decide +kernel
theorem kb_2480_44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 44 27 = true := by
  decide +kernel
theorem kg_2480_44 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 44 27 = true := by decide +kernel
theorem kb_2480_71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 71 1 = true := by
  decide +kernel
theorem kg_2480_71 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 71 1 = true := by decide +kernel

end B334.E1x.Pts.S707
