import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5359L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5359 of `S707`, parts 0 … 127, re-packed by predicted kernel memory (4.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K5359C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5359_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5359.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_5359_0 : IPChk.allR (Pts.glueIB K5359.lits KW_5359) 0 1 = true := by decide +kernel
theorem kb_5359_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5359.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_5359_1 : IPChk.allR (Pts.glueIB K5359.lits KW_5359) 1 1 = true := by decide +kernel
theorem kb_5359_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5359.lits.getD i 0)) 2 3 = true := by
  decide +kernel
theorem kg_5359_2 : IPChk.allR (Pts.glueIB K5359.lits KW_5359) 2 3 = true := by decide +kernel
theorem kb_5359_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5359.lits.getD i 0)) 5 13 = true := by
  decide +kernel
theorem kg_5359_5 : IPChk.allR (Pts.glueIB K5359.lits KW_5359) 5 13 = true := by decide +kernel
theorem kb_5359_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5359.lits.getD i 0)) 18 110 = true := by
  decide +kernel
theorem kg_5359_18 : IPChk.allR (Pts.glueIB K5359.lits KW_5359) 18 110 = true := by decide +kernel

end B334.E1x.Pts.S707
