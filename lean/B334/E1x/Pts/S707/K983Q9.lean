import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K983L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 983 of `S707`, parts 828 … 879, re-packed by predicted kernel memory (1.82 of 8.19 GB;
stage707_v5; the theorems are v3's `K983C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_983_828 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 828 21 = true := by
  decide +kernel
theorem kg_983_828 : IPChk.allR (Pts.glueIB K983.lits KW_983) 828 21 = true := by decide +kernel
theorem kb_983_849 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 849 29 = true := by
  decide +kernel
theorem kg_983_849 : IPChk.allR (Pts.glueIB K983.lits KW_983) 849 29 = true := by decide +kernel
theorem kb_983_878 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 878 2 = true := by
  decide +kernel
theorem kg_983_878 : IPChk.allR (Pts.glueIB K983.lits KW_983) 878 2 = true := by decide +kernel

end B334.E1x.Pts.S707
