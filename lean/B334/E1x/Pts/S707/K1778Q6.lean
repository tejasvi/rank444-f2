import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1778L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1778 of `S707`, parts 693 … 800, re-packed by predicted kernel memory (2.97 of 8.19 GB;
stage707_v5; the theorems are v3's `K1778C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1778_693 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 693 19 = true := by
  decide +kernel
theorem kg_1778_693 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 693 19 = true := by decide +kernel
theorem kb_1778_712 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 712 23 = true := by
  decide +kernel
theorem kg_1778_712 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 712 23 = true := by decide +kernel
theorem kb_1778_735 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 735 30 = true := by
  decide +kernel
theorem kg_1778_735 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 735 30 = true := by decide +kernel
theorem kb_1778_765 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 765 36 = true := by
  decide +kernel
theorem kg_1778_765 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 765 36 = true := by decide +kernel

end B334.E1x.Pts.S707
