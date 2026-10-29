import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1181L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1181 of `S707`, parts 0 … 143, re-packed by predicted kernel memory (4.71 of 8.19 GB;
stage707_v5; the theorems are v3's `K1181C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1181_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_1181_0 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 3 = true := by decide +kernel
theorem kb_1181_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 3 12 = true := by
  decide +kernel
theorem kg_1181_3 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 3 12 = true := by decide +kernel
theorem kb_1181_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 15 16 = true := by
  decide +kernel
theorem kg_1181_15 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 15 16 = true := by decide +kernel
theorem kb_1181_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 31 46 = true := by
  decide +kernel
theorem kg_1181_31 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 31 46 = true := by decide +kernel
theorem kb_1181_77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 77 23 = true := by
  decide +kernel
theorem kg_1181_77 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 77 23 = true := by decide +kernel
theorem kb_1181_100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 100 44 = true := by
  decide +kernel
theorem kg_1181_100 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 100 44 = true := by decide +kernel

end B334.E1x.Pts.S707
