import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2472L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2472 of `S707`, parts 0 … 114, re-packed by predicted kernel memory (3.15 of 8.19 GB;
stage707_v5; the theorems are v3's `K2472C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2472_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2472_0 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 1 = true := by decide +kernel
theorem kb_2472_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 1 11 = true := by
  decide +kernel
theorem kg_2472_1 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 1 11 = true := by decide +kernel
theorem kb_2472_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 12 56 = true := by
  decide +kernel
theorem kg_2472_12 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 12 56 = true := by decide +kernel
theorem kb_2472_68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 68 47 = true := by
  decide +kernel
theorem kg_2472_68 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 68 47 = true := by decide +kernel

end B334.E1x.Pts.S707
