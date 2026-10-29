import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2694L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2694 of `S707`, parts 0 … 114, re-packed by predicted kernel memory (3.11 of 8.19 GB;
stage707_v5; the theorems are v3's `K2694C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2694_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2694.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2694_0 : IPChk.allR (Pts.glueIB K2694.lits KW_2694) 0 1 = true := by decide +kernel
theorem kb_2694_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2694.lits.getD i 0)) 1 12 = true := by
  decide +kernel
theorem kg_2694_1 : IPChk.allR (Pts.glueIB K2694.lits KW_2694) 1 12 = true := by decide +kernel
theorem kb_2694_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2694.lits.getD i 0)) 13 55 = true := by
  decide +kernel
theorem kg_2694_13 : IPChk.allR (Pts.glueIB K2694.lits KW_2694) 13 55 = true := by decide +kernel
theorem kb_2694_68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2694.lits.getD i 0)) 68 47 = true := by
  decide +kernel
theorem kg_2694_68 : IPChk.allR (Pts.glueIB K2694.lits KW_2694) 68 47 = true := by decide +kernel

end B334.E1x.Pts.S707
