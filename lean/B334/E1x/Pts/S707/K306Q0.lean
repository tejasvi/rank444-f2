import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K306L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 306 of `S707`, parts 0 … 96, re-packed by predicted kernel memory (7.34 of 8.19 GB;
stage707_v5; the theorems are v3's `K306C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_306_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_306_0 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 1 = true := by decide +kernel
theorem kb_306_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_306_1 : IPChk.allR (Pts.glueIB K306.lits KW_306) 1 2 = true := by decide +kernel
theorem kb_306_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 3 29 = true := by
  decide +kernel
theorem kg_306_3 : IPChk.allR (Pts.glueIB K306.lits KW_306) 3 29 = true := by decide +kernel
theorem kb_306_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 32 2 = true := by
  decide +kernel
theorem kg_306_32 : IPChk.allR (Pts.glueIB K306.lits KW_306) 32 2 = true := by decide +kernel
theorem kb_306_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 34 6 = true := by
  decide +kernel
theorem kg_306_34 : IPChk.allR (Pts.glueIB K306.lits KW_306) 34 6 = true := by decide +kernel
theorem kb_306_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 40 2 = true := by
  decide +kernel
theorem kg_306_40 : IPChk.allR (Pts.glueIB K306.lits KW_306) 40 2 = true := by decide +kernel
theorem kb_306_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 42 30 = true := by
  decide +kernel
theorem kg_306_42 : IPChk.allR (Pts.glueIB K306.lits KW_306) 42 30 = true := by decide +kernel
theorem kb_306_72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 72 14 = true := by
  decide +kernel
theorem kg_306_72 : IPChk.allR (Pts.glueIB K306.lits KW_306) 72 14 = true := by decide +kernel
theorem kb_306_86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 86 11 = true := by
  decide +kernel
theorem kg_306_86 : IPChk.allR (Pts.glueIB K306.lits KW_306) 86 11 = true := by decide +kernel

end B334.E1x.Pts.S707
