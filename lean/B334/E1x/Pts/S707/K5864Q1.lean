import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5864L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5864 of `S707`, parts 36 … 49, re-packed by predicted kernel memory (2.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K5864C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5864_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5864.lits.getD i 0)) 36 9 = true := by
  decide +kernel
theorem kg_5864_36 : IPChk.allR (Pts.glueIB K5864.lits KW_5864) 36 9 = true := by decide +kernel
theorem kb_5864_45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5864.lits.getD i 0)) 45 2 = true := by
  decide +kernel
theorem kg_5864_45 : IPChk.allR (Pts.glueIB K5864.lits KW_5864) 45 2 = true := by decide +kernel
theorem kb_5864_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5864.lits.getD i 0)) 47 3 = true := by
  decide +kernel
theorem kg_5864_47 : IPChk.allR (Pts.glueIB K5864.lits KW_5864) 47 3 = true := by decide +kernel

end B334.E1x.Pts.S707
