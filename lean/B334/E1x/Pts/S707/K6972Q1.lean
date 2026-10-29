import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6972L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6972 of `S707`, parts 28 … 34, re-packed by predicted kernel memory (3.76 of 8.19 GB;
stage707_v5; the theorems are v3's `K6972C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6972_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 28 1 = true := by
  decide +kernel
theorem kg_6972_28 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 28 1 = true := by decide +kernel
theorem kb_6972_29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 29 2 = true := by
  decide +kernel
theorem kg_6972_29 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 29 2 = true := by decide +kernel
theorem kb_6972_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 31 1 = true := by
  decide +kernel
theorem kg_6972_31 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 31 1 = true := by decide +kernel
theorem kb_6972_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 32 1 = true := by
  decide +kernel
theorem kg_6972_32 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 32 1 = true := by decide +kernel
theorem kb_6972_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 33 2 = true := by
  decide +kernel
theorem kg_6972_33 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 33 2 = true := by decide +kernel

end B334.E1x.Pts.S707
