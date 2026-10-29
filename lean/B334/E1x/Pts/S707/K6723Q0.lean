import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6723L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6723 of `S707`, parts 0 … 34, re-packed by predicted kernel memory (6.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K6723C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6723_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 0 8 = true := by
  decide +kernel
theorem kg_6723_0 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 0 8 = true := by decide +kernel
theorem kb_6723_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 8 1 = true := by
  decide +kernel
theorem kg_6723_8 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 8 1 = true := by decide +kernel
theorem kb_6723_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 9 8 = true := by
  decide +kernel
theorem kg_6723_9 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 9 8 = true := by decide +kernel
theorem kb_6723_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 17 1 = true := by
  decide +kernel
theorem kg_6723_17 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 17 1 = true := by decide +kernel
theorem kb_6723_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 18 7 = true := by
  decide +kernel
theorem kg_6723_18 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 18 7 = true := by decide +kernel
theorem kb_6723_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 25 6 = true := by
  decide +kernel
theorem kg_6723_25 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 25 6 = true := by decide +kernel
theorem kb_6723_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 31 1 = true := by
  decide +kernel
theorem kg_6723_31 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 31 1 = true := by decide +kernel
theorem kb_6723_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6723.lits.getD i 0)) 32 3 = true := by
  decide +kernel
theorem kg_6723_32 : IPChk.allR (Pts.glueIB K6723.lits KW_6723) 32 3 = true := by decide +kernel

end B334.E1x.Pts.S707
