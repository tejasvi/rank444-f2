import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1694L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1694 of `S707`, parts 600 … 679, re-packed by predicted kernel memory (2.18 of 8.19 GB;
stage707_v5; the theorems are v3's `K1694C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1694_600 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1694.lits.getD i 0)) 600 14 = true := by
  decide +kernel
theorem kg_1694_600 : IPChk.allR (Pts.glueIB K1694.lits KW_1694) 600 14 = true := by decide +kernel
theorem kb_1694_614 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1694.lits.getD i 0)) 614 33 = true := by
  decide +kernel
theorem kg_1694_614 : IPChk.allR (Pts.glueIB K1694.lits KW_1694) 614 33 = true := by decide +kernel
theorem kb_1694_647 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1694.lits.getD i 0)) 647 33 = true := by
  decide +kernel
theorem kg_1694_647 : IPChk.allR (Pts.glueIB K1694.lits KW_1694) 647 33 = true := by decide +kernel

end B334.E1x.Pts.S707
