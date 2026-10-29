import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1780L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1780 of `S707`, parts 808 … 843, re-packed by predicted kernel memory (2.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K1780C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1780_808 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 808 2 = true := by
  decide +kernel
theorem kg_1780_808 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 808 2 = true := by decide +kernel
theorem kb_1780_810 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 810 13 = true := by
  decide +kernel
theorem kg_1780_810 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 810 13 = true := by decide +kernel
theorem kb_1780_823 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 823 6 = true := by
  decide +kernel
theorem kg_1780_823 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 823 6 = true := by decide +kernel
theorem kb_1780_829 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 829 15 = true := by
  decide +kernel
theorem kg_1780_829 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 829 15 = true := by decide +kernel

end B334.E1x.Pts.S707
