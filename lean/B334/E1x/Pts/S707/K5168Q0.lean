import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5168L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5168 of `S707`, parts 0 … 15, re-packed by predicted kernel memory (2.25 of 8.19 GB;
stage707_v5; the theorems are v3's `K5168C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5168_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5168.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_5168_0 : IPChk.allR (Pts.glueIB K5168.lits KW_5168) 0 4 = true := by decide +kernel
theorem kb_5168_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5168.lits.getD i 0)) 4 11 = true := by
  decide +kernel
theorem kg_5168_4 : IPChk.allR (Pts.glueIB K5168.lits KW_5168) 4 11 = true := by decide +kernel
theorem kb_5168_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5168.lits.getD i 0)) 15 1 = true := by
  decide +kernel
theorem kg_5168_15 : IPChk.allR (Pts.glueIB K5168.lits KW_5168) 15 1 = true := by decide +kernel

end B334.E1x.Pts.S707
