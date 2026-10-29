import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4653L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4653 of `S707`, parts 0 … 40, re-packed by predicted kernel memory (1.93 of 8.19 GB;
stage707_v5; the theorems are v3's `K4653C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4653_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4653.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4653_0 : IPChk.allR (Pts.glueIB K4653.lits KW_4653) 0 2 = true := by decide +kernel
theorem kb_4653_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4653.lits.getD i 0)) 2 25 = true := by
  decide +kernel
theorem kg_4653_2 : IPChk.allR (Pts.glueIB K4653.lits KW_4653) 2 25 = true := by decide +kernel
theorem kb_4653_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4653.lits.getD i 0)) 27 14 = true := by
  decide +kernel
theorem kg_4653_27 : IPChk.allR (Pts.glueIB K4653.lits KW_4653) 27 14 = true := by decide +kernel

end B334.E1x.Pts.S707
