import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5242L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5242 of `S707`, parts 253 … 268, re-packed by predicted kernel memory (2.30 of 8.19 GB;
stage707_v5; the theorems are v3's `K5242C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5242_253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5242.lits.getD i 0)) 253 11 = true := by
  decide +kernel
theorem kg_5242_253 : IPChk.allR (Pts.glueIB K5242.lits KW_5242) 253 11 = true := by decide +kernel
theorem kb_5242_264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5242.lits.getD i 0)) 264 2 = true := by
  decide +kernel
theorem kg_5242_264 : IPChk.allR (Pts.glueIB K5242.lits KW_5242) 264 2 = true := by decide +kernel
theorem kb_5242_266 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5242.lits.getD i 0)) 266 3 = true := by
  decide +kernel
theorem kg_5242_266 : IPChk.allR (Pts.glueIB K5242.lits KW_5242) 266 3 = true := by decide +kernel

end B334.E1x.Pts.S707
