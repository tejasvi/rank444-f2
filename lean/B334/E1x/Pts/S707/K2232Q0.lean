import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2232L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2232 of `S707`, parts 0 … 112, re-packed by predicted kernel memory (3.18 of 8.19 GB;
stage707_v5; the theorems are v3's `K2232C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2232_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2232.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2232_0 : IPChk.allR (Pts.glueIB K2232.lits KW_2232) 0 1 = true := by decide +kernel
theorem kb_2232_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2232.lits.getD i 0)) 1 11 = true := by
  decide +kernel
theorem kg_2232_1 : IPChk.allR (Pts.glueIB K2232.lits KW_2232) 1 11 = true := by decide +kernel
theorem kb_2232_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2232.lits.getD i 0)) 12 55 = true := by
  decide +kernel
theorem kg_2232_12 : IPChk.allR (Pts.glueIB K2232.lits KW_2232) 12 55 = true := by decide +kernel
theorem kb_2232_67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2232.lits.getD i 0)) 67 46 = true := by
  decide +kernel
theorem kg_2232_67 : IPChk.allR (Pts.glueIB K2232.lits KW_2232) 67 46 = true := by decide +kernel

end B334.E1x.Pts.S707
