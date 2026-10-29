import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3022L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3022 of `S707`, parts 160 … 211, re-packed by predicted kernel memory (7.41 of 8.19 GB;
stage707_v5; the theorems are v3's `K3022C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3022_160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 160 7 = true := by
  decide +kernel
theorem kg_3022_160 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 160 7 = true := by decide +kernel
theorem kb_3022_167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 167 2 = true := by
  decide +kernel
theorem kg_3022_167 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 167 2 = true := by decide +kernel
theorem kb_3022_169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 169 6 = true := by
  decide +kernel
theorem kg_3022_169 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 169 6 = true := by decide +kernel
theorem kb_3022_175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 175 2 = true := by
  decide +kernel
theorem kg_3022_175 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 175 2 = true := by decide +kernel
theorem kb_3022_177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 177 2 = true := by
  decide +kernel
theorem kg_3022_177 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 177 2 = true := by decide +kernel
theorem kb_3022_179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 179 1 = true := by
  decide +kernel
theorem kg_3022_179 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 179 1 = true := by decide +kernel
theorem kb_3022_180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 180 1 = true := by
  decide +kernel
theorem kg_3022_180 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 180 1 = true := by decide +kernel
theorem kb_3022_181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 181 29 = true := by
  decide +kernel
theorem kg_3022_181 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 181 29 = true := by decide +kernel
theorem kb_3022_210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 210 2 = true := by
  decide +kernel
theorem kg_3022_210 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 210 2 = true := by decide +kernel

end B334.E1x.Pts.S707
