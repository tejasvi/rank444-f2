import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5482L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5482 of `S707`, parts 123 … 229, re-packed by predicted kernel memory (4.90 of 8.19 GB;
stage707_v5; the theorems are v3's `K5482C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5482_123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 123 2 = true := by
  decide +kernel
theorem kg_5482_123 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 123 2 = true := by decide +kernel
theorem kb_5482_125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 125 18 = true := by
  decide +kernel
theorem kg_5482_125 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 125 18 = true := by decide +kernel
theorem kb_5482_143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 143 30 = true := by
  decide +kernel
theorem kg_5482_143 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 143 30 = true := by decide +kernel
theorem kb_5482_173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 173 2 = true := by
  decide +kernel
theorem kg_5482_173 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 173 2 = true := by decide +kernel
theorem kb_5482_175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 175 8 = true := by
  decide +kernel
theorem kg_5482_175 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 175 8 = true := by decide +kernel
theorem kb_5482_183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 183 19 = true := by
  decide +kernel
theorem kg_5482_183 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 183 19 = true := by decide +kernel
theorem kb_5482_202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5482.lits.getD i 0)) 202 28 = true := by
  decide +kernel
theorem kg_5482_202 : IPChk.allR (Pts.glueIB K5482.lits KW_5482) 202 28 = true := by decide +kernel

end B334.E1x.Pts.S707
