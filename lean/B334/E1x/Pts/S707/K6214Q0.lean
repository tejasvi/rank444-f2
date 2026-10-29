import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6214L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6214 of `S707`, parts 0 … 25, re-packed by predicted kernel memory (1.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K6214C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6214_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6214.lits.getD i 0)) 0 8 = true := by
  decide +kernel
theorem kg_6214_0 : IPChk.allR (Pts.glueIB K6214.lits KW_6214) 0 8 = true := by decide +kernel
theorem kb_6214_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6214.lits.getD i 0)) 8 18 = true := by
  decide +kernel
theorem kg_6214_8 : IPChk.allR (Pts.glueIB K6214.lits KW_6214) 8 18 = true := by decide +kernel

end B334.E1x.Pts.S707
