import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3972L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3972 of `S707`, parts 0 … 2, re-packed by predicted kernel memory (0.96 of 8.19 GB;
stage707_v5; the theorems are v3's `K3972C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3972_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3972.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3972_0 : IPChk.allR (Pts.glueIB K3972.lits KW_3972) 0 2 = true := by decide +kernel
theorem kb_3972_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3972.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_3972_2 : IPChk.allR (Pts.glueIB K3972.lits KW_3972) 2 1 = true := by decide +kernel

end B334.E1x.Pts.S707
