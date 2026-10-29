import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5977L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5977 of `S707`, parts 0 … 20, re-packed by predicted kernel memory (1.48 of 8.19 GB;
stage707_v5; the theorems are v3's `K5977C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5977_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5977.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_5977_0 : IPChk.allR (Pts.glueIB K5977.lits KW_5977) 0 9 = true := by decide +kernel
theorem kb_5977_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5977.lits.getD i 0)) 9 4 = true := by
  decide +kernel
theorem kg_5977_9 : IPChk.allR (Pts.glueIB K5977.lits KW_5977) 9 4 = true := by decide +kernel
theorem kb_5977_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5977.lits.getD i 0)) 13 8 = true := by
  decide +kernel
theorem kg_5977_13 : IPChk.allR (Pts.glueIB K5977.lits KW_5977) 13 8 = true := by decide +kernel

end B334.E1x.Pts.S707
