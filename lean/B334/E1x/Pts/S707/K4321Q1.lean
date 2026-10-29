import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4321L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4321 of `S707`, parts 150 … 189, re-packed by predicted kernel memory (1.61 of 8.19 GB;
stage707_v5; the theorems are v3's `K4321C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4321_150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4321.lits.getD i 0)) 150 9 = true := by
  decide +kernel
theorem kg_4321_150 : IPChk.allR (Pts.glueIB K4321.lits KW_4321) 150 9 = true := by decide +kernel
theorem kb_4321_159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4321.lits.getD i 0)) 159 31 = true := by
  decide +kernel
theorem kg_4321_159 : IPChk.allR (Pts.glueIB K4321.lits KW_4321) 159 31 = true := by decide +kernel

end B334.E1x.Pts.S707
