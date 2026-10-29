import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K846L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 846 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (2.66 of 8.19 GB;
stage707_v5; the theorems are v3's `K846C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_846_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_846_0 : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 1 = true := by decide +kernel
theorem kb_846_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_846_1 : IPChk.allR (Pts.glueIB K846.lits KW_846) 1 1 = true := by decide +kernel
theorem kb_846_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 2 4 = true := by
  decide +kernel
theorem kg_846_2 : IPChk.allR (Pts.glueIB K846.lits KW_846) 2 4 = true := by decide +kernel
theorem kb_846_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 6 2 = true := by
  decide +kernel
theorem kg_846_6 : IPChk.allR (Pts.glueIB K846.lits KW_846) 6 2 = true := by decide +kernel

end B334.E1x.Pts.S707
