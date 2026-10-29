import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5244L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5244 of `S707`, parts 93 … 179, re-packed by predicted kernel memory (2.81 of 8.19 GB;
stage707_v5; the theorems are v3's `K5244C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5244_93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5244.lits.getD i 0)) 93 28 = true := by
  decide +kernel
theorem kg_5244_93 : IPChk.allR (Pts.glueIB K5244.lits KW_5244) 93 28 = true := by decide +kernel
theorem kb_5244_121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5244.lits.getD i 0)) 121 4 = true := by
  decide +kernel
theorem kg_5244_121 : IPChk.allR (Pts.glueIB K5244.lits KW_5244) 121 4 = true := by decide +kernel
theorem kb_5244_125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5244.lits.getD i 0)) 125 34 = true := by
  decide +kernel
theorem kg_5244_125 : IPChk.allR (Pts.glueIB K5244.lits KW_5244) 125 34 = true := by decide +kernel
theorem kb_5244_159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5244.lits.getD i 0)) 159 21 = true := by
  decide +kernel
theorem kg_5244_159 : IPChk.allR (Pts.glueIB K5244.lits KW_5244) 159 21 = true := by decide +kernel

end B334.E1x.Pts.S707
