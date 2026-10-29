import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6273L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6273 of `S707`, parts 0 … 35, re-packed by predicted kernel memory (4.57 of 8.19 GB;
stage707_v5; the theorems are v3's `K6273C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6273_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_6273_0 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 0 4 = true := by decide +kernel
theorem kb_6273_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_6273_4 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 4 1 = true := by decide +kernel
theorem kb_6273_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 5 18 = true := by
  decide +kernel
theorem kg_6273_5 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 5 18 = true := by decide +kernel
theorem kb_6273_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 23 1 = true := by
  decide +kernel
theorem kg_6273_23 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 23 1 = true := by decide +kernel
theorem kb_6273_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 24 11 = true := by
  decide +kernel
theorem kg_6273_24 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 24 11 = true := by decide +kernel
theorem kb_6273_35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6273.lits.getD i 0)) 35 1 = true := by
  decide +kernel
theorem kg_6273_35 : IPChk.allR (Pts.glueIB K6273.lits KW_6273) 35 1 = true := by decide +kernel

end B334.E1x.Pts.S707
