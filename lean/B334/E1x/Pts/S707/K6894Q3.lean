import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6894L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6894 of `S707`, parts 189 … 209, re-packed by predicted kernel memory (3.60 of 8.19 GB;
stage707_v5; the theorems are v3's `K6894C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6894_189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 189 4 = true := by
  decide +kernel
theorem kg_6894_189 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 189 4 = true := by decide +kernel
theorem kb_6894_193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 193 9 = true := by
  decide +kernel
theorem kg_6894_193 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 193 9 = true := by decide +kernel
theorem kb_6894_202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 202 2 = true := by
  decide +kernel
theorem kg_6894_202 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 202 2 = true := by decide +kernel
theorem kb_6894_204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 204 2 = true := by
  decide +kernel
theorem kg_6894_204 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 204 2 = true := by decide +kernel
theorem kb_6894_206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 206 4 = true := by
  decide +kernel
theorem kg_6894_206 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 206 4 = true := by decide +kernel

end B334.E1x.Pts.S707
