import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1035L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1035 of `S707`, parts 299 … 329, re-packed by predicted kernel memory (4.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K1035C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1035_299 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 299 3 = true := by
  decide +kernel
theorem kg_1035_299 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 299 3 = true := by decide +kernel
theorem kb_1035_302 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 302 1 = true := by
  decide +kernel
theorem kg_1035_302 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 302 1 = true := by decide +kernel
theorem kb_1035_303 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 303 5 = true := by
  decide +kernel
theorem kg_1035_303 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 303 5 = true := by decide +kernel
theorem kb_1035_308 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 308 10 = true := by
  decide +kernel
theorem kg_1035_308 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 308 10 = true := by decide +kernel
theorem kb_1035_318 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 318 9 = true := by
  decide +kernel
theorem kg_1035_318 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 318 9 = true := by decide +kernel
theorem kb_1035_327 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 327 3 = true := by
  decide +kernel
theorem kg_1035_327 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 327 3 = true := by decide +kernel

end B334.E1x.Pts.S707
