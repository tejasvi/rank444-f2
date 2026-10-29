import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5911L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5911 of `S707`, parts 408 … 421, re-packed by predicted kernel memory (2.56 of 8.19 GB;
stage707_v5; the theorems are v3's `K5911C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5911_408 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5911.lits.getD i 0)) 408 4 = true := by
  decide +kernel
theorem kg_5911_408 : IPChk.allR (Pts.glueIB K5911.lits KW_5911) 408 4 = true := by decide +kernel
theorem kb_5911_412 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5911.lits.getD i 0)) 412 6 = true := by
  decide +kernel
theorem kg_5911_412 : IPChk.allR (Pts.glueIB K5911.lits KW_5911) 412 6 = true := by decide +kernel
theorem kb_5911_418 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5911.lits.getD i 0)) 418 3 = true := by
  decide +kernel
theorem kg_5911_418 : IPChk.allR (Pts.glueIB K5911.lits KW_5911) 418 3 = true := by decide +kernel
theorem kb_5911_421 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5911.lits.getD i 0)) 421 1 = true := by
  decide +kernel
theorem kg_5911_421 : IPChk.allR (Pts.glueIB K5911.lits KW_5911) 421 1 = true := by decide +kernel

end B334.E1x.Pts.S707
