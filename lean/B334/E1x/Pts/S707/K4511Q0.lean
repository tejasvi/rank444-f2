import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4511L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4511 of `S707`, parts 0 … 18, re-packed by predicted kernel memory (1.40 of 8.19 GB;
stage707_v5; the theorems are v3's `K4511C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4511_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4511.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_4511_0 : IPChk.allR (Pts.glueIB K4511.lits KW_4511) 0 6 = true := by decide +kernel
theorem kb_4511_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4511.lits.getD i 0)) 6 13 = true := by
  decide +kernel
theorem kg_4511_6 : IPChk.allR (Pts.glueIB K4511.lits KW_4511) 6 13 = true := by decide +kernel

end B334.E1x.Pts.S707
