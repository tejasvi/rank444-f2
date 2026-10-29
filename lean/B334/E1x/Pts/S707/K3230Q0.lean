import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3230L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3230 of `S707`, parts 0 … 22, re-packed by predicted kernel memory (2.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K3230C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3230_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3230.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3230_0 : IPChk.allR (Pts.glueIB K3230.lits KW_3230) 0 2 = true := by decide +kernel
theorem kb_3230_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3230.lits.getD i 0)) 2 12 = true := by
  decide +kernel
theorem kg_3230_2 : IPChk.allR (Pts.glueIB K3230.lits KW_3230) 2 12 = true := by decide +kernel
theorem kb_3230_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3230.lits.getD i 0)) 14 9 = true := by
  decide +kernel
theorem kg_3230_14 : IPChk.allR (Pts.glueIB K3230.lits KW_3230) 14 9 = true := by decide +kernel

end B334.E1x.Pts.S707
