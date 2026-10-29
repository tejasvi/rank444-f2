import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5172L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5172 of `S707`, parts 0 … 9, re-packed by predicted kernel memory (2.35 of 8.19 GB;
stage707_v5; the theorems are v3's `K5172C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5172_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5172.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_5172_0 : IPChk.allR (Pts.glueIB K5172.lits KW_5172) 0 5 = true := by decide +kernel
theorem kb_5172_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5172.lits.getD i 0)) 5 3 = true := by
  decide +kernel
theorem kg_5172_5 : IPChk.allR (Pts.glueIB K5172.lits KW_5172) 5 3 = true := by decide +kernel
theorem kb_5172_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5172.lits.getD i 0)) 8 2 = true := by
  decide +kernel
theorem kg_5172_8 : IPChk.allR (Pts.glueIB K5172.lits KW_5172) 8 2 = true := by decide +kernel

end B334.E1x.Pts.S707
