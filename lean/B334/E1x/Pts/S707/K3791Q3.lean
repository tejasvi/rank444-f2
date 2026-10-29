import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3791L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3791 of `S707`, parts 457 … 616, re-packed by predicted kernel memory (3.91 of 8.19 GB;
stage707_v5; the theorems are v3's `K3791C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3791_457 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3791.lits.getD i 0)) 457 6 = true := by
  decide +kernel
theorem kg_3791_457 : IPChk.allR (Pts.glueIB K3791.lits KW_3791) 457 6 = true := by decide +kernel
theorem kb_3791_463 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3791.lits.getD i 0)) 463 101 = true := by
  decide +kernel
theorem kg_3791_463 : IPChk.allR (Pts.glueIB K3791.lits KW_3791) 463 101 = true := by decide +kernel
theorem kb_3791_564 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3791.lits.getD i 0)) 564 46 = true := by
  decide +kernel
theorem kg_3791_564 : IPChk.allR (Pts.glueIB K3791.lits KW_3791) 564 46 = true := by decide +kernel
theorem kb_3791_610 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3791.lits.getD i 0)) 610 3 = true := by
  decide +kernel
theorem kg_3791_610 : IPChk.allR (Pts.glueIB K3791.lits KW_3791) 610 3 = true := by decide +kernel
theorem kb_3791_613 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3791.lits.getD i 0)) 613 4 = true := by
  decide +kernel
theorem kg_3791_613 : IPChk.allR (Pts.glueIB K3791.lits KW_3791) 613 4 = true := by decide +kernel

end B334.E1x.Pts.S707
