import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4043L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4043 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (1.94 of 8.19 GB;
stage707_v5; the theorems are v3's `K4043C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4043_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4043.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_4043_0 : IPChk.allR (Pts.glueIB K4043.lits KW_4043) 0 1 = true := by decide +kernel
theorem kb_4043_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4043.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_4043_1 : IPChk.allR (Pts.glueIB K4043.lits KW_4043) 1 1 = true := by decide +kernel
theorem kb_4043_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4043.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_4043_2 : IPChk.allR (Pts.glueIB K4043.lits KW_4043) 2 2 = true := by decide +kernel

end B334.E1x.Pts.S707
