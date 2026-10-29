import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6576L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6576 of `S707`, parts 0 … 50, re-packed by predicted kernel memory (2.80 of 8.19 GB;
stage707_v5; the theorems are v3's `K6576C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6576_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6576.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_6576_0 : IPChk.allR (Pts.glueIB K6576.lits KW_6576) 0 2 = true := by decide +kernel
theorem kb_6576_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6576.lits.getD i 0)) 2 23 = true := by
  decide +kernel
theorem kg_6576_2 : IPChk.allR (Pts.glueIB K6576.lits KW_6576) 2 23 = true := by decide +kernel
theorem kb_6576_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6576.lits.getD i 0)) 25 21 = true := by
  decide +kernel
theorem kg_6576_25 : IPChk.allR (Pts.glueIB K6576.lits KW_6576) 25 21 = true := by decide +kernel
theorem kb_6576_46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6576.lits.getD i 0)) 46 5 = true := by
  decide +kernel
theorem kg_6576_46 : IPChk.allR (Pts.glueIB K6576.lits KW_6576) 46 5 = true := by decide +kernel

end B334.E1x.Pts.S707
