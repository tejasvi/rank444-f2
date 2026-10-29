import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6274L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6274 of `S707`, parts 229 … 310, re-packed by predicted kernel memory (1.13 of 8.19 GB;
stage707_v5; the theorems are v3's `K6274C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6274_229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6274.lits.getD i 0)) 229 62 = true := by
  decide +kernel
theorem kg_6274_229 : IPChk.allR (Pts.glueIB K6274.lits KW_6274) 229 62 = true := by decide +kernel
theorem kb_6274_291 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6274.lits.getD i 0)) 291 20 = true := by
  decide +kernel
theorem kg_6274_291 : IPChk.allR (Pts.glueIB K6274.lits KW_6274) 291 20 = true := by decide +kernel

end B334.E1x.Pts.S707
