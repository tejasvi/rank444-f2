import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3029L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3029 of `S707`, parts 347 … 536, re-packed by predicted kernel memory (3.32 of 8.19 GB;
stage707_v5; the theorems are v3's `K3029C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3029_347 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 347 39 = true := by
  decide +kernel
theorem kg_3029_347 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 347 39 = true := by decide +kernel
theorem kb_3029_386 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 386 20 = true := by
  decide +kernel
theorem kg_3029_386 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 386 20 = true := by decide +kernel
theorem kb_3029_406 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 406 94 = true := by
  decide +kernel
theorem kg_3029_406 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 406 94 = true := by decide +kernel
theorem kb_3029_500 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 500 35 = true := by
  decide +kernel
theorem kg_3029_500 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 500 35 = true := by decide +kernel
theorem kb_3029_535 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 535 2 = true := by
  decide +kernel
theorem kg_3029_535 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 535 2 = true := by decide +kernel

end B334.E1x.Pts.S707
