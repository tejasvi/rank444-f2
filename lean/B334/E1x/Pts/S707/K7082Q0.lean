import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7082L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7082 of `S707`, parts 0 … 39, re-packed by predicted kernel memory (3.49 of 8.19 GB;
stage707_v5; the theorems are v3's `K7082C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7082_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_7082_0 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 2 = true := by decide +kernel
theorem kb_7082_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 2 18 = true := by
  decide +kernel
theorem kg_7082_2 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 2 18 = true := by decide +kernel
theorem kb_7082_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 20 4 = true := by
  decide +kernel
theorem kg_7082_20 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 20 4 = true := by decide +kernel
theorem kb_7082_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 24 9 = true := by
  decide +kernel
theorem kg_7082_24 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 24 9 = true := by decide +kernel
theorem kb_7082_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 33 7 = true := by
  decide +kernel
theorem kg_7082_33 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 33 7 = true := by decide +kernel

end B334.E1x.Pts.S707
