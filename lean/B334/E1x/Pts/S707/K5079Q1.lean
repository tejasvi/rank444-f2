import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5079L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5079 of `S707`, parts 63 … 77, re-packed by predicted kernel memory (4.26 of 8.19 GB;
stage707_v5; the theorems are v3's `K5079C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5079_63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 63 7 = true := by
  decide +kernel
theorem kg_5079_63 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 63 7 = true := by decide +kernel
theorem kb_5079_70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 70 2 = true := by
  decide +kernel
theorem kg_5079_70 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 70 2 = true := by decide +kernel
theorem kb_5079_72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 72 1 = true := by
  decide +kernel
theorem kg_5079_72 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 72 1 = true := by decide +kernel
theorem kb_5079_73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 73 2 = true := by
  decide +kernel
theorem kg_5079_73 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 73 2 = true := by decide +kernel
theorem kb_5079_75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 75 2 = true := by
  decide +kernel
theorem kg_5079_75 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 75 2 = true := by decide +kernel
theorem kb_5079_77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5079.lits.getD i 0)) 77 1 = true := by
  decide +kernel
theorem kg_5079_77 : IPChk.allR (Pts.glueIB K5079.lits KW_5079) 77 1 = true := by decide +kernel

end B334.E1x.Pts.S707
