import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5995L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5995 of `S707`, parts 0 … 24, re-packed by predicted kernel memory (4.70 of 8.19 GB;
stage707_v5; the theorems are v3's `K5995C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5995_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_5995_0 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 0 3 = true := by decide +kernel
theorem kb_5995_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_5995_3 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 3 1 = true := by decide +kernel
theorem kb_5995_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 4 7 = true := by
  decide +kernel
theorem kg_5995_4 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 4 7 = true := by decide +kernel
theorem kb_5995_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 11 4 = true := by
  decide +kernel
theorem kg_5995_11 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 11 4 = true := by decide +kernel
theorem kb_5995_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 15 5 = true := by
  decide +kernel
theorem kg_5995_15 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 15 5 = true := by decide +kernel
theorem kb_5995_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5995.lits.getD i 0)) 20 5 = true := by
  decide +kernel
theorem kg_5995_20 : IPChk.allR (Pts.glueIB K5995.lits KW_5995) 20 5 = true := by decide +kernel

end B334.E1x.Pts.S707
