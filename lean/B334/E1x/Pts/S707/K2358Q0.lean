import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2358L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2358 of `S707`, parts 0 … 25, re-packed by predicted kernel memory (1.81 of 8.19 GB;
stage707_v5; the theorems are v3's `K2358C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2358_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2358.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_2358_0 : IPChk.allR (Pts.glueIB K2358.lits KW_2358) 0 3 = true := by decide +kernel
theorem kb_2358_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2358.lits.getD i 0)) 3 22 = true := by
  decide +kernel
theorem kg_2358_3 : IPChk.allR (Pts.glueIB K2358.lits KW_2358) 3 22 = true := by decide +kernel
theorem kb_2358_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2358.lits.getD i 0)) 25 1 = true := by
  decide +kernel
theorem kg_2358_25 : IPChk.allR (Pts.glueIB K2358.lits KW_2358) 25 1 = true := by decide +kernel

end B334.E1x.Pts.S707
