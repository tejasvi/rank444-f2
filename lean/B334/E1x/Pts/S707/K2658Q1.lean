import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2658L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2658 of `S707`, parts 81 … 113, re-packed by predicted kernel memory (1.01 of 8.19 GB;
stage707_v5; the theorems are v3's `K2658C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2658_81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2658.lits.getD i 0)) 81 23 = true := by
  decide +kernel
theorem kg_2658_81 : IPChk.allR (Pts.glueIB K2658.lits KW_2658) 81 23 = true := by decide +kernel
theorem kb_2658_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2658.lits.getD i 0)) 104 10 = true := by
  decide +kernel
theorem kg_2658_104 : IPChk.allR (Pts.glueIB K2658.lits KW_2658) 104 10 = true := by decide +kernel

end B334.E1x.Pts.S707
