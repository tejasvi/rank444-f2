import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4160L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4160 of `S707`, parts 111 … 120, re-packed by predicted kernel memory (2.16 of 8.19 GB;
stage707_v5; the theorems are v3's `K4160C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4160_111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 111 4 = true := by
  decide +kernel
theorem kg_4160_111 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 111 4 = true := by decide +kernel
theorem kb_4160_115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 115 4 = true := by
  decide +kernel
theorem kg_4160_115 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 115 4 = true := by decide +kernel
theorem kb_4160_119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 119 2 = true := by
  decide +kernel
theorem kg_4160_119 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 119 2 = true := by decide +kernel

end B334.E1x.Pts.S707
