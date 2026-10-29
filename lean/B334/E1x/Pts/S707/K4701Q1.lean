import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4701L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4701 of `S707`, parts 141 … 265, re-packed by predicted kernel memory (6.30 of 8.19 GB;
stage707_v5; the theorems are v3's `K4701C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4701_141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 141 14 = true := by
  decide +kernel
theorem kg_4701_141 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 141 14 = true := by decide +kernel
theorem kb_4701_155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 155 5 = true := by
  decide +kernel
theorem kg_4701_155 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 155 5 = true := by decide +kernel
theorem kb_4701_160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 160 2 = true := by
  decide +kernel
theorem kg_4701_160 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 160 2 = true := by decide +kernel
theorem kb_4701_162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 162 16 = true := by
  decide +kernel
theorem kg_4701_162 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 162 16 = true := by decide +kernel
theorem kb_4701_178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 178 9 = true := by
  decide +kernel
theorem kg_4701_178 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 178 9 = true := by decide +kernel
theorem kb_4701_187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 187 25 = true := by
  decide +kernel
theorem kg_4701_187 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 187 25 = true := by decide +kernel
theorem kb_4701_212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 212 20 = true := by
  decide +kernel
theorem kg_4701_212 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 212 20 = true := by decide +kernel
theorem kb_4701_232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4701.lits.getD i 0)) 232 34 = true := by
  decide +kernel
theorem kg_4701_232 : IPChk.allR (Pts.glueIB K4701.lits KW_4701) 232 34 = true := by decide +kernel

end B334.E1x.Pts.S707
