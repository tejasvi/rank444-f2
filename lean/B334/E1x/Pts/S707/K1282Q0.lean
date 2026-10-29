import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1282L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1282 of `S707`, parts 0 … 6, re-packed by predicted kernel memory (4.01 of 8.19 GB;
stage707_v5; the theorems are v3's `K1282C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1282_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_1282_0 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 1 = true := by decide +kernel
theorem kb_1282_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_1282_1 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 1 1 = true := by decide +kernel
theorem kb_1282_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_1282_2 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 2 1 = true := by decide +kernel
theorem kb_1282_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 3 2 = true := by
  decide +kernel
theorem kg_1282_3 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 3 2 = true := by decide +kernel
theorem kb_1282_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_1282_5 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 5 2 = true := by decide +kernel

end B334.E1x.Pts.S707
