import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4546L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4546 of `S707`, parts 212 … 233, re-packed by predicted kernel memory (5.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K4546C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4546_212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 212 3 = true := by
  decide +kernel
theorem kg_4546_212 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 212 3 = true := by decide +kernel
theorem kb_4546_215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 215 3 = true := by
  decide +kernel
theorem kg_4546_215 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 215 3 = true := by decide +kernel
theorem kb_4546_218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 218 5 = true := by
  decide +kernel
theorem kg_4546_218 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 218 5 = true := by decide +kernel
theorem kb_4546_223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 223 2 = true := by
  decide +kernel
theorem kg_4546_223 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 223 2 = true := by decide +kernel
theorem kb_4546_225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 225 6 = true := by
  decide +kernel
theorem kg_4546_225 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 225 6 = true := by decide +kernel
theorem kb_4546_231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 231 2 = true := by
  decide +kernel
theorem kg_4546_231 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 231 2 = true := by decide +kernel
theorem kb_4546_233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4546.lits.getD i 0)) 233 1 = true := by
  decide +kernel
theorem kg_4546_233 : IPChk.allR (Pts.glueIB K4546.lits KW_4546) 233 1 = true := by decide +kernel

end B334.E1x.Pts.S707
