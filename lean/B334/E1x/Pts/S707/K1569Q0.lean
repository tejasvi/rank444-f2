import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1569L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1569 of `S707`, parts 0 … 43, re-packed by predicted kernel memory (1.98 of 8.19 GB;
stage707_v5; the theorems are v3's `K1569C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1569_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1569.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_1569_0 : IPChk.allR (Pts.glueIB K1569.lits KW_1569) 0 2 = true := by decide +kernel
theorem kb_1569_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1569.lits.getD i 0)) 2 22 = true := by
  decide +kernel
theorem kg_1569_2 : IPChk.allR (Pts.glueIB K1569.lits KW_1569) 2 22 = true := by decide +kernel
theorem kb_1569_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1569.lits.getD i 0)) 24 20 = true := by
  decide +kernel
theorem kg_1569_24 : IPChk.allR (Pts.glueIB K1569.lits KW_1569) 24 20 = true := by decide +kernel

end B334.E1x.Pts.S707
