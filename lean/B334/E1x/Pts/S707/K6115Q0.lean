import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6115L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6115 of `S707`, parts 0 … 3, re-packed by predicted kernel memory (2.40 of 8.19 GB;
stage707_v5; the theorems are v3's `K6115C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6115_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6115.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6115_0 : IPChk.allR (Pts.glueIB K6115.lits KW_6115) 0 2 = true := by decide +kernel
theorem kb_6115_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6115.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_6115_2 : IPChk.allR (Pts.glueIB K6115.lits KW_6115) 2 1 = true := by decide +kernel
theorem kb_6115_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6115.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_6115_3 : IPChk.allR (Pts.glueIB K6115.lits KW_6115) 3 1 = true := by decide +kernel

end B334.E1x.Pts.S707
