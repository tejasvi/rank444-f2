import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3342L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3342 of `S707`, parts 201 … 326, re-packed by predicted kernel memory (2.19 of 8.19 GB;
stage707_v5; the theorems are v3's `K3342C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3342_201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3342.lits.getD i 0)) 201 5 = true := by
  decide +kernel
theorem kg_3342_201 : IPChk.allR (Pts.glueIB K3342.lits KW_3342) 201 5 = true := by decide +kernel
theorem kb_3342_206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3342.lits.getD i 0)) 206 24 = true := by
  decide +kernel
theorem kg_3342_206 : IPChk.allR (Pts.glueIB K3342.lits KW_3342) 206 24 = true := by decide +kernel
theorem kb_3342_230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3342.lits.getD i 0)) 230 97 = true := by
  decide +kernel
theorem kg_3342_230 : IPChk.allR (Pts.glueIB K3342.lits KW_3342) 230 97 = true := by decide +kernel

end B334.E1x.Pts.S707
