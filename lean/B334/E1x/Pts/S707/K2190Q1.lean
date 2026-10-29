import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2190L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2190 of `S707`, parts 93 … 292, re-packed by predicted kernel memory (5.65 of 8.19 GB;
stage707_v5; the theorems are v3's `K2190C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2190_93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 93 13 = true := by
  decide +kernel
theorem kg_2190_93 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 93 13 = true := by decide +kernel
theorem kb_2190_106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 106 11 = true := by
  decide +kernel
theorem kg_2190_106 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 106 11 = true := by decide +kernel
theorem kb_2190_117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 117 30 = true := by
  decide +kernel
theorem kg_2190_117 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 117 30 = true := by decide +kernel
theorem kb_2190_147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 147 68 = true := by
  decide +kernel
theorem kg_2190_147 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 147 68 = true := by decide +kernel
theorem kb_2190_215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 215 42 = true := by
  decide +kernel
theorem kg_2190_215 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 215 42 = true := by decide +kernel
theorem kb_2190_257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 257 10 = true := by
  decide +kernel
theorem kg_2190_257 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 257 10 = true := by decide +kernel
theorem kb_2190_267 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2190.lits.getD i 0)) 267 26 = true := by
  decide +kernel
theorem kg_2190_267 : IPChk.allR (Pts.glueIB K2190.lits KW_2190) 267 26 = true := by decide +kernel

end B334.E1x.Pts.S707
