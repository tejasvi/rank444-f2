import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4021L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4021 of `S707`, parts 0 … 12, re-packed by predicted kernel memory (2.79 of 8.19 GB;
stage707_v5; the theorems are v3's `K4021C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4021_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4021.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_4021_0 : IPChk.allR (Pts.glueIB K4021.lits KW_4021) 0 9 = true := by decide +kernel
theorem kb_4021_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4021.lits.getD i 0)) 9 1 = true := by
  decide +kernel
theorem kg_4021_9 : IPChk.allR (Pts.glueIB K4021.lits KW_4021) 9 1 = true := by decide +kernel
theorem kb_4021_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4021.lits.getD i 0)) 10 2 = true := by
  decide +kernel
theorem kg_4021_10 : IPChk.allR (Pts.glueIB K4021.lits KW_4021) 10 2 = true := by decide +kernel
theorem kb_4021_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4021.lits.getD i 0)) 12 1 = true := by
  decide +kernel
theorem kg_4021_12 : IPChk.allR (Pts.glueIB K4021.lits KW_4021) 12 1 = true := by decide +kernel

end B334.E1x.Pts.S707
