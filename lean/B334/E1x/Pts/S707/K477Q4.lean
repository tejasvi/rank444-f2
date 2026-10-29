import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K477L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 477 of `S707`, parts 384 … 512, re-packed by predicted kernel memory (4.52 of 8.19 GB;
stage707_v5; the theorems are v3's `K477C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_477_384 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 384 2 = true := by
  decide +kernel
theorem kg_477_384 : IPChk.allR (Pts.glueIB K477.lits KW_477) 384 2 = true := by decide +kernel
theorem kb_477_386 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 386 8 = true := by
  decide +kernel
theorem kg_477_386 : IPChk.allR (Pts.glueIB K477.lits KW_477) 386 8 = true := by decide +kernel
theorem kb_477_394 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 394 30 = true := by
  decide +kernel
theorem kg_477_394 : IPChk.allR (Pts.glueIB K477.lits KW_477) 394 30 = true := by decide +kernel
theorem kb_477_424 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 424 38 = true := by
  decide +kernel
theorem kg_477_424 : IPChk.allR (Pts.glueIB K477.lits KW_477) 424 38 = true := by decide +kernel
theorem kb_477_462 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 462 41 = true := by
  decide +kernel
theorem kg_477_462 : IPChk.allR (Pts.glueIB K477.lits KW_477) 462 41 = true := by decide +kernel
theorem kb_477_503 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K477.lits.getD i 0)) 503 10 = true := by
  decide +kernel
theorem kg_477_503 : IPChk.allR (Pts.glueIB K477.lits KW_477) 503 10 = true := by decide +kernel

end B334.E1x.Pts.S707
