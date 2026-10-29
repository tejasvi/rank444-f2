import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5629L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5629 of `S707`, parts 0 … 10, re-packed by predicted kernel memory (1.19 of 8.19 GB;
stage707_v5; the theorems are v3's `K5629C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5629_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5629.lits.getD i 0)) 0 10 = true := by
  decide +kernel
theorem kg_5629_0 : IPChk.allR (Pts.glueIB K5629.lits KW_5629) 0 10 = true := by decide +kernel
theorem kb_5629_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5629.lits.getD i 0)) 10 1 = true := by
  decide +kernel
theorem kg_5629_10 : IPChk.allR (Pts.glueIB K5629.lits KW_5629) 10 1 = true := by decide +kernel

end B334.E1x.Pts.S707
