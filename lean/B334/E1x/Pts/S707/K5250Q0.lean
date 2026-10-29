import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5250L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5250 of `S707`, parts 0 … 50, re-packed by predicted kernel memory (4.32 of 8.19 GB;
stage707_v5; the theorems are v3's `K5250C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5250_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_5250_0 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 0 2 = true := by decide +kernel
theorem kb_5250_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_5250_2 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 2 6 = true := by decide +kernel
theorem kb_5250_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 8 5 = true := by
  decide +kernel
theorem kg_5250_8 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 8 5 = true := by decide +kernel
theorem kb_5250_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 13 20 = true := by
  decide +kernel
theorem kg_5250_13 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 13 20 = true := by decide +kernel
theorem kb_5250_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 33 17 = true := by
  decide +kernel
theorem kg_5250_33 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 33 17 = true := by decide +kernel
theorem kb_5250_50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5250.lits.getD i 0)) 50 1 = true := by
  decide +kernel
theorem kg_5250_50 : IPChk.allR (Pts.glueIB K5250.lits KW_5250) 50 1 = true := by decide +kernel

end B334.E1x.Pts.S707
