import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6600L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6600 of `S707`, parts 0 … 57, re-packed by predicted kernel memory (4.85 of 8.19 GB;
stage707_v5; the theorems are v3's `K6600C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6600_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6600_0 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 0 2 = true := by decide +kernel
theorem kb_6600_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 2 23 = true := by
  decide +kernel
theorem kg_6600_2 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 2 23 = true := by decide +kernel
theorem kb_6600_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 25 17 = true := by
  decide +kernel
theorem kg_6600_25 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 25 17 = true := by decide +kernel
theorem kb_6600_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 42 10 = true := by
  decide +kernel
theorem kg_6600_42 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 42 10 = true := by decide +kernel
theorem kb_6600_52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 52 4 = true := by
  decide +kernel
theorem kg_6600_52 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 52 4 = true := by decide +kernel
theorem kb_6600_56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6600.lits.getD i 0)) 56 2 = true := by
  decide +kernel
theorem kg_6600_56 : IPChk.allR (Pts.glueIB K6600.lits KW_6600) 56 2 = true := by decide +kernel

end B334.E1x.Pts.S707
