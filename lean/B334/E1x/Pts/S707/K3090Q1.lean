import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3090L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3090 of `S707`, parts 68 … 84, re-packed by predicted kernel memory (2.40 of 8.19 GB;
stage707_v5; the theorems are v3's `K3090C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3090_68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3090.lits.getD i 0)) 68 14 = true := by
  decide +kernel
theorem kg_3090_68 : IPChk.allR (Pts.glueIB K3090.lits KW_3090) 68 14 = true := by decide +kernel
theorem kb_3090_82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3090.lits.getD i 0)) 82 2 = true := by
  decide +kernel
theorem kg_3090_82 : IPChk.allR (Pts.glueIB K3090.lits KW_3090) 82 2 = true := by decide +kernel
theorem kb_3090_84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3090.lits.getD i 0)) 84 1 = true := by
  decide +kernel
theorem kg_3090_84 : IPChk.allR (Pts.glueIB K3090.lits KW_3090) 84 1 = true := by decide +kernel

end B334.E1x.Pts.S707
