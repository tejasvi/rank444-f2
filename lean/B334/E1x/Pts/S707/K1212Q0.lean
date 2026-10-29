import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1212L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1212 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (1.95 of 8.19 GB;
stage707_v5; the theorems are v3's `K1212C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1212_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_1212_0 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 0 1 = true := by decide +kernel
theorem kb_1212_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_1212_1 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 1 1 = true := by decide +kernel
theorem kb_1212_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_1212_2 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 2 1 = true := by decide +kernel

end B334.E1x.Pts.S707
