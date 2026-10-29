import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5126L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5126 of `S707`, parts 0 … 27, re-packed by predicted kernel memory (1.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K5126C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5126_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5126.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_5126_0 : IPChk.allR (Pts.glueIB K5126.lits KW_5126) 0 6 = true := by decide +kernel
theorem kb_5126_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5126.lits.getD i 0)) 6 22 = true := by
  decide +kernel
theorem kg_5126_6 : IPChk.allR (Pts.glueIB K5126.lits KW_5126) 6 22 = true := by decide +kernel

end B334.E1x.Pts.S707
