import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1738L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1738 of `S707`, parts 0 … 107, re-packed by predicted kernel memory (4.75 of 8.19 GB;
stage707_v5; the theorems are v3's `K1738C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1738_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_1738_0 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 2 = true := by decide +kernel
theorem kb_1738_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 2 28 = true := by
  decide +kernel
theorem kg_1738_2 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 2 28 = true := by decide +kernel
theorem kb_1738_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 30 16 = true := by
  decide +kernel
theorem kg_1738_30 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 30 16 = true := by decide +kernel
theorem kb_1738_46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 46 28 = true := by
  decide +kernel
theorem kg_1738_46 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 46 28 = true := by decide +kernel
theorem kb_1738_74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 74 6 = true := by
  decide +kernel
theorem kg_1738_74 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 74 6 = true := by decide +kernel
theorem kb_1738_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 80 28 = true := by
  decide +kernel
theorem kg_1738_80 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 80 28 = true := by decide +kernel

end B334.E1x.Pts.S707
