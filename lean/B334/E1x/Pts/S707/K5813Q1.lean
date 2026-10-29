import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5813L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5813 of `S707`, parts 65 … 96, re-packed by predicted kernel memory (5.10 of 8.19 GB;
stage707_v5; the theorems are v3's `K5813C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5813_65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 65 4 = true := by
  decide +kernel
theorem kg_5813_65 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 65 4 = true := by decide +kernel
theorem kb_5813_69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 69 6 = true := by
  decide +kernel
theorem kg_5813_69 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 69 6 = true := by decide +kernel
theorem kb_5813_75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 75 11 = true := by
  decide +kernel
theorem kg_5813_75 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 75 11 = true := by decide +kernel
theorem kb_5813_86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 86 3 = true := by
  decide +kernel
theorem kg_5813_86 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 86 3 = true := by decide +kernel
theorem kb_5813_89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 89 4 = true := by
  decide +kernel
theorem kg_5813_89 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 89 4 = true := by decide +kernel
theorem kb_5813_93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5813.lits.getD i 0)) 93 4 = true := by
  decide +kernel
theorem kg_5813_93 : IPChk.allR (Pts.glueIB K5813.lits KW_5813) 93 4 = true := by decide +kernel

end B334.E1x.Pts.S707
