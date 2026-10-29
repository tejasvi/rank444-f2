import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1782L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1782 of `S707`, parts 583 … 693, re-packed by predicted kernel memory (4.08 of 8.19 GB;
stage707_v5; the theorems are v3's `K1782C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1782_583 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 583 9 = true := by
  decide +kernel
theorem kg_1782_583 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 583 9 = true := by decide +kernel
theorem kb_1782_592 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 592 28 = true := by
  decide +kernel
theorem kg_1782_592 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 592 28 = true := by decide +kernel
theorem kb_1782_620 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 620 13 = true := by
  decide +kernel
theorem kg_1782_620 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 620 13 = true := by decide +kernel
theorem kb_1782_633 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 633 33 = true := by
  decide +kernel
theorem kg_1782_633 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 633 33 = true := by decide +kernel
theorem kb_1782_666 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 666 28 = true := by
  decide +kernel
theorem kg_1782_666 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 666 28 = true := by decide +kernel

end B334.E1x.Pts.S707
