import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5006L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5006 of `S707`, parts 0 … 53, re-packed by predicted kernel memory (4.79 of 8.19 GB;
stage707_v5; the theorems are v3's `K5006C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5006_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_5006_0 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 0 2 = true := by decide +kernel
theorem kb_5006_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_5006_2 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 2 1 = true := by decide +kernel
theorem kb_5006_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 3 8 = true := by
  decide +kernel
theorem kg_5006_3 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 3 8 = true := by decide +kernel
theorem kb_5006_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 11 26 = true := by
  decide +kernel
theorem kg_5006_11 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 11 26 = true := by decide +kernel
theorem kb_5006_37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 37 5 = true := by
  decide +kernel
theorem kg_5006_37 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 37 5 = true := by decide +kernel
theorem kb_5006_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 42 11 = true := by
  decide +kernel
theorem kg_5006_42 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 42 11 = true := by decide +kernel
theorem kb_5006_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5006.lits.getD i 0)) 53 1 = true := by
  decide +kernel
theorem kg_5006_53 : IPChk.allR (Pts.glueIB K5006.lits KW_5006) 53 1 = true := by decide +kernel

end B334.E1x.Pts.S707
