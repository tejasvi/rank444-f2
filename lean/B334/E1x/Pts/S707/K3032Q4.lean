import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3032L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3032 of `S707`, parts 578 … 688, re-packed by predicted kernel memory (2.78 of 8.19 GB;
stage707_v5; the theorems are v3's `K3032C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3032_578 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 578 50 = true := by
  decide +kernel
theorem kg_3032_578 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 578 50 = true := by decide +kernel
theorem kb_3032_628 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 628 8 = true := by
  decide +kernel
theorem kg_3032_628 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 628 8 = true := by decide +kernel
theorem kb_3032_636 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 636 32 = true := by
  decide +kernel
theorem kg_3032_636 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 636 32 = true := by decide +kernel
theorem kb_3032_668 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 668 21 = true := by
  decide +kernel
theorem kg_3032_668 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 668 21 = true := by decide +kernel

end B334.E1x.Pts.S707
