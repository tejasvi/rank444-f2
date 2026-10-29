import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5803L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5803 of `S707`, parts 15 … 18, re-packed by predicted kernel memory (1.95 of 8.19 GB;
stage707_v5; the theorems are v3's `K5803C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5803_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5803.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_5803_15 : IPChk.allR (Pts.glueIB K5803.lits KW_5803) 15 2 = true := by decide +kernel
theorem kb_5803_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5803.lits.getD i 0)) 17 1 = true := by
  decide +kernel
theorem kg_5803_17 : IPChk.allR (Pts.glueIB K5803.lits KW_5803) 17 1 = true := by decide +kernel
theorem kb_5803_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5803.lits.getD i 0)) 18 1 = true := by
  decide +kernel
theorem kg_5803_18 : IPChk.allR (Pts.glueIB K5803.lits KW_5803) 18 1 = true := by decide +kernel

end B334.E1x.Pts.S707
