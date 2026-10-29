import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6236L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6236 of `S707`, parts 0 … 6, re-packed by predicted kernel memory (4.19 of 8.19 GB;
stage707_v5; the theorems are v3's `K6236C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6236_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6236_0 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 0 2 = true := by decide +kernel
theorem kb_6236_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_6236_2 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 2 1 = true := by decide +kernel
theorem kb_6236_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_6236_3 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 3 1 = true := by decide +kernel
theorem kb_6236_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_6236_4 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 4 1 = true := by decide +kernel
theorem kb_6236_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 5 1 = true := by
  decide +kernel
theorem kg_6236_5 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 5 1 = true := by decide +kernel
theorem kb_6236_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6236.lits.getD i 0)) 6 1 = true := by
  decide +kernel
theorem kg_6236_6 : IPChk.allR (Pts.glueIB K6236.lits KW_6236) 6 1 = true := by decide +kernel

end B334.E1x.Pts.S707
