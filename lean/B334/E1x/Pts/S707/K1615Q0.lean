import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1615L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1615 of `S707`, parts 0 … 17, re-packed by predicted kernel memory (4.01 of 8.19 GB;
stage707_v5; the theorems are v3's `K1615C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1615_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_1615_0 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 0 9 = true := by decide +kernel
theorem kb_1615_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_1615_9 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 9 2 = true := by decide +kernel
theorem kb_1615_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 11 3 = true := by
  decide +kernel
theorem kg_1615_11 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 11 3 = true := by decide +kernel
theorem kb_1615_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 14 1 = true := by
  decide +kernel
theorem kg_1615_14 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 14 1 = true := by decide +kernel
theorem kb_1615_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 15 1 = true := by
  decide +kernel
theorem kg_1615_15 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 15 1 = true := by decide +kernel
theorem kb_1615_16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1615.lits.getD i 0)) 16 2 = true := by
  decide +kernel
theorem kg_1615_16 : IPChk.allR (Pts.glueIB K1615.lits KW_1615) 16 2 = true := by decide +kernel

end B334.E1x.Pts.S707
