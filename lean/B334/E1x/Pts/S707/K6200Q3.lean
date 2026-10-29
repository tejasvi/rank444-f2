import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6200L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6200 of `S707`, parts 169 … 183, re-packed by predicted kernel memory (5.10 of 8.19 GB;
stage707_v5; the theorems are v3's `K6200C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6200_169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 169 1 = true := by
  decide +kernel
theorem kg_6200_169 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 169 1 = true := by decide +kernel
theorem kb_6200_170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 170 1 = true := by
  decide +kernel
theorem kg_6200_170 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 170 1 = true := by decide +kernel
theorem kb_6200_171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 171 2 = true := by
  decide +kernel
theorem kg_6200_171 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 171 2 = true := by decide +kernel
theorem kb_6200_173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 173 3 = true := by
  decide +kernel
theorem kg_6200_173 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 173 3 = true := by decide +kernel
theorem kb_6200_176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 176 3 = true := by
  decide +kernel
theorem kg_6200_176 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 176 3 = true := by decide +kernel
theorem kb_6200_179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 179 2 = true := by
  decide +kernel
theorem kg_6200_179 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 179 2 = true := by decide +kernel
theorem kb_6200_181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6200.lits.getD i 0)) 181 3 = true := by
  decide +kernel
theorem kg_6200_181 : IPChk.allR (Pts.glueIB K6200.lits KW_6200) 181 3 = true := by decide +kernel

end B334.E1x.Pts.S707
