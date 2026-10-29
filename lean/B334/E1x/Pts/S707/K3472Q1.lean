import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3472L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3472 of `S707`, parts 95 … 139, re-packed by predicted kernel memory (1.04 of 8.19 GB;
stage707_v5; the theorems are v3's `K3472C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3472_95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3472.lits.getD i 0)) 95 32 = true := by
  decide +kernel
theorem kg_3472_95 : IPChk.allR (Pts.glueIB K3472.lits KW_3472) 95 32 = true := by decide +kernel
theorem kb_3472_127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3472.lits.getD i 0)) 127 13 = true := by
  decide +kernel
theorem kg_3472_127 : IPChk.allR (Pts.glueIB K3472.lits KW_3472) 127 13 = true := by decide +kernel

end B334.E1x.Pts.S707
