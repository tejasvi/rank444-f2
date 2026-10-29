import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2128L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2128 of `S707`, parts 0 … 31, re-packed by predicted kernel memory (1.98 of 8.19 GB;
stage707_v5; the theorems are v3's `K2128C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2128_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2128.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_2128_0 : IPChk.allR (Pts.glueIB K2128.lits KW_2128) 0 9 = true := by decide +kernel
theorem kb_2128_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2128.lits.getD i 0)) 9 8 = true := by
  decide +kernel
theorem kg_2128_9 : IPChk.allR (Pts.glueIB K2128.lits KW_2128) 9 8 = true := by decide +kernel
theorem kb_2128_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2128.lits.getD i 0)) 17 15 = true := by
  decide +kernel
theorem kg_2128_17 : IPChk.allR (Pts.glueIB K2128.lits KW_2128) 17 15 = true := by decide +kernel

end B334.E1x.Pts.S707
