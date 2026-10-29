import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2263L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2263 of `S707`, parts 113 … 174, re-packed by predicted kernel memory (3.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K2263C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2263_113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2263.lits.getD i 0)) 113 14 = true := by
  decide +kernel
theorem kg_2263_113 : IPChk.allR (Pts.glueIB K2263.lits KW_2263) 113 14 = true := by decide +kernel
theorem kb_2263_127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2263.lits.getD i 0)) 127 13 = true := by
  decide +kernel
theorem kg_2263_127 : IPChk.allR (Pts.glueIB K2263.lits KW_2263) 127 13 = true := by decide +kernel
theorem kb_2263_140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2263.lits.getD i 0)) 140 15 = true := by
  decide +kernel
theorem kg_2263_140 : IPChk.allR (Pts.glueIB K2263.lits KW_2263) 140 15 = true := by decide +kernel
theorem kb_2263_155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2263.lits.getD i 0)) 155 20 = true := by
  decide +kernel
theorem kg_2263_155 : IPChk.allR (Pts.glueIB K2263.lits KW_2263) 155 20 = true := by decide +kernel

end B334.E1x.Pts.S707
