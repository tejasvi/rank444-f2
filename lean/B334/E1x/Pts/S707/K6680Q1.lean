import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6680L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6680 of `S707`, parts 42 … 44, re-packed by predicted kernel memory (1.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K6680C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6680_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6680.lits.getD i 0)) 42 2 = true := by
  decide +kernel
theorem kg_6680_42 : IPChk.allR (Pts.glueIB K6680.lits KW_6680) 42 2 = true := by decide +kernel
theorem kb_6680_44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6680.lits.getD i 0)) 44 1 = true := by
  decide +kernel
theorem kg_6680_44 : IPChk.allR (Pts.glueIB K6680.lits KW_6680) 44 1 = true := by decide +kernel

end B334.E1x.Pts.S707
