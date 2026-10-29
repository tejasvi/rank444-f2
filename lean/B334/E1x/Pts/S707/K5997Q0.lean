import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5997L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5997 of `S707`, parts 0 … 14, re-packed by predicted kernel memory (2.46 of 8.19 GB;
stage707_v5; the theorems are v3's `K5997C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5997_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5997.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_5997_0 : IPChk.allR (Pts.glueIB K5997.lits KW_5997) 0 2 = true := by decide +kernel
theorem kb_5997_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5997.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_5997_2 : IPChk.allR (Pts.glueIB K5997.lits KW_5997) 2 1 = true := by decide +kernel
theorem kb_5997_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5997.lits.getD i 0)) 3 11 = true := by
  decide +kernel
theorem kg_5997_3 : IPChk.allR (Pts.glueIB K5997.lits KW_5997) 3 11 = true := by decide +kernel
theorem kb_5997_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5997.lits.getD i 0)) 14 1 = true := by
  decide +kernel
theorem kg_5997_14 : IPChk.allR (Pts.glueIB K5997.lits KW_5997) 14 1 = true := by decide +kernel

end B334.E1x.Pts.S707
