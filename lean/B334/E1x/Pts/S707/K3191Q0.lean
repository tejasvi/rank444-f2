import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3191L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3191 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (2.91 of 8.19 GB;
stage707_v5; the theorems are v3's `K3191C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3191_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3191.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_3191_0 : IPChk.allR (Pts.glueIB K3191.lits KW_3191) 0 1 = true := by decide +kernel
theorem kb_3191_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3191.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_3191_1 : IPChk.allR (Pts.glueIB K3191.lits KW_3191) 1 1 = true := by decide +kernel
theorem kb_3191_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3191.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_3191_2 : IPChk.allR (Pts.glueIB K3191.lits KW_3191) 2 2 = true := by decide +kernel
theorem kb_3191_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3191.lits.getD i 0)) 4 3 = true := by
  decide +kernel
theorem kg_3191_4 : IPChk.allR (Pts.glueIB K3191.lits KW_3191) 4 3 = true := by decide +kernel
theorem kb_3191_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3191.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_3191_7 : IPChk.allR (Pts.glueIB K3191.lits KW_3191) 7 1 = true := by decide +kernel

end B334.E1x.Pts.S707
