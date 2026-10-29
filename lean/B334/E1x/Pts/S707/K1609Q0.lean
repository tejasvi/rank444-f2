import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1609L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1609 of `S707`, parts 0 … 35, re-packed by predicted kernel memory (3.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K1609C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1609_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1609.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_1609_0 : IPChk.allR (Pts.glueIB K1609.lits KW_1609) 0 3 = true := by decide +kernel
theorem kb_1609_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1609.lits.getD i 0)) 3 10 = true := by
  decide +kernel
theorem kg_1609_3 : IPChk.allR (Pts.glueIB K1609.lits KW_1609) 3 10 = true := by decide +kernel
theorem kb_1609_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1609.lits.getD i 0)) 13 18 = true := by
  decide +kernel
theorem kg_1609_13 : IPChk.allR (Pts.glueIB K1609.lits KW_1609) 13 18 = true := by decide +kernel
theorem kb_1609_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1609.lits.getD i 0)) 31 1 = true := by
  decide +kernel
theorem kg_1609_31 : IPChk.allR (Pts.glueIB K1609.lits KW_1609) 31 1 = true := by decide +kernel
theorem kb_1609_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1609.lits.getD i 0)) 32 4 = true := by
  decide +kernel
theorem kg_1609_32 : IPChk.allR (Pts.glueIB K1609.lits KW_1609) 32 4 = true := by decide +kernel

end B334.E1x.Pts.S707
