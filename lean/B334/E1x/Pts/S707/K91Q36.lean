import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K91L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 91 of `S707`, parts 6480 … 6507, re-packed by predicted kernel memory (3.38 of 8.19 GB;
stage707_v5; the theorems are v3's `K91C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_91_6480 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 6480 1 = true := by
  decide +kernel
theorem kg_91_6480 : IPChk.allR (Pts.glueIB K91.lits KW_91) 6480 1 = true := by decide +kernel
theorem kb_91_6481 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 6481 5 = true := by
  decide +kernel
theorem kg_91_6481 : IPChk.allR (Pts.glueIB K91.lits KW_91) 6481 5 = true := by decide +kernel
theorem kb_91_6486 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 6486 18 = true := by
  decide +kernel
theorem kg_91_6486 : IPChk.allR (Pts.glueIB K91.lits KW_91) 6486 18 = true := by decide +kernel
theorem kb_91_6504 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 6504 3 = true := by
  decide +kernel
theorem kg_91_6504 : IPChk.allR (Pts.glueIB K91.lits KW_91) 6504 3 = true := by decide +kernel
theorem kb_91_6507 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 6507 1 = true := by
  decide +kernel
theorem kg_91_6507 : IPChk.allR (Pts.glueIB K91.lits KW_91) 6507 1 = true := by decide +kernel

end B334.E1x.Pts.S707
