import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4282L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4282 of `S707`, parts 155 … 212, re-packed by predicted kernel memory (1.83 of 8.19 GB;
stage707_v5; the theorems are v3's `K4282C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4282_155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4282.lits.getD i 0)) 155 9 = true := by
  decide +kernel
theorem kg_4282_155 : IPChk.allR (Pts.glueIB K4282.lits KW_4282) 155 9 = true := by decide +kernel
theorem kb_4282_164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4282.lits.getD i 0)) 164 44 = true := by
  decide +kernel
theorem kg_4282_164 : IPChk.allR (Pts.glueIB K4282.lits KW_4282) 164 44 = true := by decide +kernel
theorem kb_4282_208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4282.lits.getD i 0)) 208 5 = true := by
  decide +kernel
theorem kg_4282_208 : IPChk.allR (Pts.glueIB K4282.lits KW_4282) 208 5 = true := by decide +kernel

end B334.E1x.Pts.S707
