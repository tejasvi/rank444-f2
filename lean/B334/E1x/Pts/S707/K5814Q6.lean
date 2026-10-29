import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5814L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5814 of `S707`, parts 245 … 253, re-packed by predicted kernel memory (3.76 of 8.19 GB;
stage707_v5; the theorems are v3's `K5814C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5814_245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5814.lits.getD i 0)) 245 2 = true := by
  decide +kernel
theorem kg_5814_245 : IPChk.allR (Pts.glueIB K5814.lits KW_5814) 245 2 = true := by decide +kernel
theorem kb_5814_247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5814.lits.getD i 0)) 247 3 = true := by
  decide +kernel
theorem kg_5814_247 : IPChk.allR (Pts.glueIB K5814.lits KW_5814) 247 3 = true := by decide +kernel
theorem kb_5814_250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5814.lits.getD i 0)) 250 1 = true := by
  decide +kernel
theorem kg_5814_250 : IPChk.allR (Pts.glueIB K5814.lits KW_5814) 250 1 = true := by decide +kernel
theorem kb_5814_251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5814.lits.getD i 0)) 251 2 = true := by
  decide +kernel
theorem kg_5814_251 : IPChk.allR (Pts.glueIB K5814.lits KW_5814) 251 2 = true := by decide +kernel
theorem kb_5814_253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5814.lits.getD i 0)) 253 1 = true := by
  decide +kernel
theorem kg_5814_253 : IPChk.allR (Pts.glueIB K5814.lits KW_5814) 253 1 = true := by decide +kernel

end B334.E1x.Pts.S707
