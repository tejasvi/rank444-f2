import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6203L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6203 of `S707`, parts 49 … 80, re-packed by predicted kernel memory (5.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K6203C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6203_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 49 8 = true := by
  decide +kernel
theorem kg_6203_49 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 49 8 = true := by decide +kernel
theorem kb_6203_57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 57 7 = true := by
  decide +kernel
theorem kg_6203_57 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 57 7 = true := by decide +kernel
theorem kb_6203_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 64 6 = true := by
  decide +kernel
theorem kg_6203_64 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 64 6 = true := by decide +kernel
theorem kb_6203_70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 70 2 = true := by
  decide +kernel
theorem kg_6203_70 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 70 2 = true := by decide +kernel
theorem kb_6203_72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 72 4 = true := by
  decide +kernel
theorem kg_6203_72 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 72 4 = true := by decide +kernel
theorem kb_6203_76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 76 3 = true := by
  decide +kernel
theorem kg_6203_76 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 76 3 = true := by decide +kernel
theorem kb_6203_79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6203.lits.getD i 0)) 79 2 = true := by
  decide +kernel
theorem kg_6203_79 : IPChk.allR (Pts.glueIB K6203.lits KW_6203) 79 2 = true := by decide +kernel

end B334.E1x.Pts.S707
