import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6332L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6332 of `S707`, parts 0 … 64, re-packed by predicted kernel memory (3.44 of 8.19 GB;
stage707_v5; the theorems are v3's `K6332C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6332_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6332.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_6332_0 : IPChk.allR (Pts.glueIB K6332.lits KW_6332) 0 11 = true := by decide +kernel
theorem kb_6332_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6332.lits.getD i 0)) 11 2 = true := by
  decide +kernel
theorem kg_6332_11 : IPChk.allR (Pts.glueIB K6332.lits KW_6332) 11 2 = true := by decide +kernel
theorem kb_6332_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6332.lits.getD i 0)) 13 20 = true := by
  decide +kernel
theorem kg_6332_13 : IPChk.allR (Pts.glueIB K6332.lits KW_6332) 13 20 = true := by decide +kernel
theorem kb_6332_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6332.lits.getD i 0)) 33 32 = true := by
  decide +kernel
theorem kg_6332_33 : IPChk.allR (Pts.glueIB K6332.lits KW_6332) 33 32 = true := by decide +kernel

end B334.E1x.Pts.S707
