import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2966L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2966 of `S707`, parts 950 … 957, re-packed by predicted kernel memory (3.28 of 8.19 GB;
stage707_v5; the theorems are v3's `K2966C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2966_950 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 950 1 = true := by
  decide +kernel
theorem kg_2966_950 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 950 1 = true := by decide +kernel
theorem kb_2966_951 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 951 1 = true := by
  decide +kernel
theorem kg_2966_951 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 951 1 = true := by decide +kernel
theorem kb_2966_952 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 952 1 = true := by
  decide +kernel
theorem kg_2966_952 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 952 1 = true := by decide +kernel
theorem kb_2966_953 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 953 3 = true := by
  decide +kernel
theorem kg_2966_953 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 953 3 = true := by decide +kernel
theorem kb_2966_956 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 956 2 = true := by
  decide +kernel
theorem kg_2966_956 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 956 2 = true := by decide +kernel

end B334.E1x.Pts.S707
