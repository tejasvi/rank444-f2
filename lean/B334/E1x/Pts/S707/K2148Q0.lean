import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2148L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2148 of `S707`, parts 0 … 52, re-packed by predicted kernel memory (2.50 of 8.19 GB;
stage707_v5; the theorems are v3's `K2148C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2148_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2148.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2148_0 : IPChk.allR (Pts.glueIB K2148.lits KW_2148) 0 2 = true := by decide +kernel
theorem kb_2148_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2148.lits.getD i 0)) 2 10 = true := by
  decide +kernel
theorem kg_2148_2 : IPChk.allR (Pts.glueIB K2148.lits KW_2148) 2 10 = true := by decide +kernel
theorem kb_2148_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2148.lits.getD i 0)) 12 41 = true := by
  decide +kernel
theorem kg_2148_12 : IPChk.allR (Pts.glueIB K2148.lits KW_2148) 12 41 = true := by decide +kernel

end B334.E1x.Pts.S707
