import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4164L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4164 of `S707`, parts 15 … 20, re-packed by predicted kernel memory (2.90 of 8.19 GB;
stage707_v5; the theorems are v3's `K4164C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4164_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4164.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_4164_15 : IPChk.allR (Pts.glueIB K4164.lits KW_4164) 15 2 = true := by decide +kernel
theorem kb_4164_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4164.lits.getD i 0)) 17 2 = true := by
  decide +kernel
theorem kg_4164_17 : IPChk.allR (Pts.glueIB K4164.lits KW_4164) 17 2 = true := by decide +kernel
theorem kb_4164_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4164.lits.getD i 0)) 19 1 = true := by
  decide +kernel
theorem kg_4164_19 : IPChk.allR (Pts.glueIB K4164.lits KW_4164) 19 1 = true := by decide +kernel
theorem kb_4164_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4164.lits.getD i 0)) 20 1 = true := by
  decide +kernel
theorem kg_4164_20 : IPChk.allR (Pts.glueIB K4164.lits KW_4164) 20 1 = true := by decide +kernel

end B334.E1x.Pts.S707
