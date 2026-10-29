import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2614L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2614 of `S707`, parts 0 … 96, re-packed by predicted kernel memory (2.89 of 8.19 GB;
stage707_v5; the theorems are v3's `K2614C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2614_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2614.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2614_0 : IPChk.allR (Pts.glueIB K2614.lits KW_2614) 0 1 = true := by decide +kernel
theorem kb_2614_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2614.lits.getD i 0)) 1 10 = true := by
  decide +kernel
theorem kg_2614_1 : IPChk.allR (Pts.glueIB K2614.lits KW_2614) 1 10 = true := by decide +kernel
theorem kb_2614_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2614.lits.getD i 0)) 11 57 = true := by
  decide +kernel
theorem kg_2614_11 : IPChk.allR (Pts.glueIB K2614.lits KW_2614) 11 57 = true := by decide +kernel
theorem kb_2614_68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2614.lits.getD i 0)) 68 29 = true := by
  decide +kernel
theorem kg_2614_68 : IPChk.allR (Pts.glueIB K2614.lits KW_2614) 68 29 = true := by decide +kernel

end B334.E1x.Pts.S707
