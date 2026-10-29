import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6116L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6116 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (4.39 of 8.19 GB;
stage707_v5; the theorems are v3's `K6116C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6116_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_6116_0 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 0 1 = true := by decide +kernel
theorem kb_6116_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_6116_1 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 1 1 = true := by decide +kernel
theorem kb_6116_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_6116_2 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 2 1 = true := by decide +kernel
theorem kb_6116_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_6116_3 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 3 1 = true := by decide +kernel
theorem kb_6116_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_6116_4 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 4 1 = true := by decide +kernel
theorem kb_6116_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_6116_5 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 5 2 = true := by decide +kernel
theorem kb_6116_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6116.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_6116_7 : IPChk.allR (Pts.glueIB K6116.lits KW_6116) 7 1 = true := by decide +kernel

end B334.E1x.Pts.S707
