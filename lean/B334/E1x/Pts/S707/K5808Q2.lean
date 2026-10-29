import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5808L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5808 of `S707`, parts 89 … 106, re-packed by predicted kernel memory (3.57 of 8.19 GB;
stage707_v5; the theorems are v3's `K5808C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5808_89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5808.lits.getD i 0)) 89 2 = true := by
  decide +kernel
theorem kg_5808_89 : IPChk.allR (Pts.glueIB K5808.lits KW_5808) 89 2 = true := by decide +kernel
theorem kb_5808_91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5808.lits.getD i 0)) 91 4 = true := by
  decide +kernel
theorem kg_5808_91 : IPChk.allR (Pts.glueIB K5808.lits KW_5808) 91 4 = true := by decide +kernel
theorem kb_5808_95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5808.lits.getD i 0)) 95 3 = true := by
  decide +kernel
theorem kg_5808_95 : IPChk.allR (Pts.glueIB K5808.lits KW_5808) 95 3 = true := by decide +kernel
theorem kb_5808_98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5808.lits.getD i 0)) 98 6 = true := by
  decide +kernel
theorem kg_5808_98 : IPChk.allR (Pts.glueIB K5808.lits KW_5808) 98 6 = true := by decide +kernel
theorem kb_5808_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5808.lits.getD i 0)) 104 3 = true := by
  decide +kernel
theorem kg_5808_104 : IPChk.allR (Pts.glueIB K5808.lits KW_5808) 104 3 = true := by decide +kernel

end B334.E1x.Pts.S707
