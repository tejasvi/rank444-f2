import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K954L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 954 of `S707`, parts 156 … 163, re-packed by predicted kernel memory (3.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K954C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_954_156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 156 2 = true := by
  decide +kernel
theorem kg_954_156 : IPChk.allR (Pts.glueIB K954.lits KW_954) 156 2 = true := by decide +kernel
theorem kb_954_158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 158 2 = true := by
  decide +kernel
theorem kg_954_158 : IPChk.allR (Pts.glueIB K954.lits KW_954) 158 2 = true := by decide +kernel
theorem kb_954_160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 160 1 = true := by
  decide +kernel
theorem kg_954_160 : IPChk.allR (Pts.glueIB K954.lits KW_954) 160 1 = true := by decide +kernel
theorem kb_954_161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 161 2 = true := by
  decide +kernel
theorem kg_954_161 : IPChk.allR (Pts.glueIB K954.lits KW_954) 161 2 = true := by decide +kernel
theorem kb_954_163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 163 1 = true := by
  decide +kernel
theorem kg_954_163 : IPChk.allR (Pts.glueIB K954.lits KW_954) 163 1 = true := by decide +kernel

end B334.E1x.Pts.S707
