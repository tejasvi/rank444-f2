import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6676L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6676 of `S707`, parts 180 … 191, re-packed by predicted kernel memory (4.79 of 8.19 GB;
stage707_v5; the theorems are v3's `K6676C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6676_180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 180 1 = true := by
  decide +kernel
theorem kg_6676_180 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 180 1 = true := by decide +kernel
theorem kb_6676_181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 181 3 = true := by
  decide +kernel
theorem kg_6676_181 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 181 3 = true := by decide +kernel
theorem kb_6676_184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 184 2 = true := by
  decide +kernel
theorem kg_6676_184 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 184 2 = true := by decide +kernel
theorem kb_6676_186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 186 1 = true := by
  decide +kernel
theorem kg_6676_186 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 186 1 = true := by decide +kernel
theorem kb_6676_187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 187 2 = true := by
  decide +kernel
theorem kg_6676_187 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 187 2 = true := by decide +kernel
theorem kb_6676_189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6676.lits.getD i 0)) 189 3 = true := by
  decide +kernel
theorem kg_6676_189 : IPChk.allR (Pts.glueIB K6676.lits KW_6676) 189 3 = true := by decide +kernel

end B334.E1x.Pts.S707
