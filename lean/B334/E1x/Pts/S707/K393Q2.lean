import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K393L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 393 of `S707`, parts 115 … 188, re-packed by predicted kernel memory (4.74 of 8.19 GB;
stage707_v5; the theorems are v3's `K393C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_393_115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 115 15 = true := by
  decide +kernel
theorem kg_393_115 : IPChk.allR (Pts.glueIB K393.lits KW_393) 115 15 = true := by decide +kernel
theorem kb_393_130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 130 22 = true := by
  decide +kernel
theorem kg_393_130 : IPChk.allR (Pts.glueIB K393.lits KW_393) 130 22 = true := by decide +kernel
theorem kb_393_152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 152 8 = true := by
  decide +kernel
theorem kg_393_152 : IPChk.allR (Pts.glueIB K393.lits KW_393) 152 8 = true := by decide +kernel
theorem kb_393_160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 160 2 = true := by
  decide +kernel
theorem kg_393_160 : IPChk.allR (Pts.glueIB K393.lits KW_393) 160 2 = true := by decide +kernel
theorem kb_393_162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 162 1 = true := by
  decide +kernel
theorem kg_393_162 : IPChk.allR (Pts.glueIB K393.lits KW_393) 162 1 = true := by decide +kernel
theorem kb_393_163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 163 1 = true := by
  decide +kernel
theorem kg_393_163 : IPChk.allR (Pts.glueIB K393.lits KW_393) 163 1 = true := by decide +kernel
theorem kb_393_164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 164 25 = true := by
  decide +kernel
theorem kg_393_164 : IPChk.allR (Pts.glueIB K393.lits KW_393) 164 25 = true := by decide +kernel

end B334.E1x.Pts.S707
