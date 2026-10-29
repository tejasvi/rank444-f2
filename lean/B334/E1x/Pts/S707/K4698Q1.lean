import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4698L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4698 of `S707`, parts 127 … 150, re-packed by predicted kernel memory (4.00 of 8.19 GB;
stage707_v5; the theorems are v3's `K4698C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4698_127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 127 8 = true := by
  decide +kernel
theorem kg_4698_127 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 127 8 = true := by decide +kernel
theorem kb_4698_135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 135 2 = true := by
  decide +kernel
theorem kg_4698_135 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 135 2 = true := by decide +kernel
theorem kb_4698_137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 137 1 = true := by
  decide +kernel
theorem kg_4698_137 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 137 1 = true := by decide +kernel
theorem kb_4698_138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 138 4 = true := by
  decide +kernel
theorem kg_4698_138 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 138 4 = true := by decide +kernel
theorem kb_4698_142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 142 7 = true := by
  decide +kernel
theorem kg_4698_142 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 142 7 = true := by decide +kernel
theorem kb_4698_149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4698.lits.getD i 0)) 149 2 = true := by
  decide +kernel
theorem kg_4698_149 : IPChk.allR (Pts.glueIB K4698.lits KW_4698) 149 2 = true := by decide +kernel

end B334.E1x.Pts.S707
