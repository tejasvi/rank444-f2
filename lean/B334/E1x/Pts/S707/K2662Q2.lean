import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2662L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2662 of `S707`, parts 294 … 341, re-packed by predicted kernel memory (2.63 of 8.19 GB;
stage707_v5; the theorems are v3's `K2662C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2662_294 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2662.lits.getD i 0)) 294 1 = true := by
  decide +kernel
theorem kg_2662_294 : IPChk.allR (Pts.glueIB K2662.lits KW_2662) 294 1 = true := by decide +kernel
theorem kb_2662_295 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2662.lits.getD i 0)) 295 9 = true := by
  decide +kernel
theorem kg_2662_295 : IPChk.allR (Pts.glueIB K2662.lits KW_2662) 295 9 = true := by decide +kernel
theorem kb_2662_304 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2662.lits.getD i 0)) 304 15 = true := by
  decide +kernel
theorem kg_2662_304 : IPChk.allR (Pts.glueIB K2662.lits KW_2662) 304 15 = true := by decide +kernel
theorem kb_2662_319 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2662.lits.getD i 0)) 319 23 = true := by
  decide +kernel
theorem kg_2662_319 : IPChk.allR (Pts.glueIB K2662.lits KW_2662) 319 23 = true := by decide +kernel

end B334.E1x.Pts.S707
