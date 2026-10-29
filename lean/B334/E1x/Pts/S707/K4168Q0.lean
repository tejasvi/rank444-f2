import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4168L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4168 of `S707`, parts 0 … 21, re-packed by predicted kernel memory (4.94 of 8.19 GB;
stage707_v5; the theorems are v3's `K4168C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4168_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4168_0 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 0 2 = true := by decide +kernel
theorem kb_4168_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 2 7 = true := by
  decide +kernel
theorem kg_4168_2 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 2 7 = true := by decide +kernel
theorem kb_4168_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 9 1 = true := by
  decide +kernel
theorem kg_4168_9 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 9 1 = true := by decide +kernel
theorem kb_4168_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 10 1 = true := by
  decide +kernel
theorem kg_4168_10 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 10 1 = true := by decide +kernel
theorem kb_4168_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 11 1 = true := by
  decide +kernel
theorem kg_4168_11 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 11 1 = true := by decide +kernel
theorem kb_4168_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 12 7 = true := by
  decide +kernel
theorem kg_4168_12 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 12 7 = true := by decide +kernel
theorem kb_4168_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4168.lits.getD i 0)) 19 3 = true := by
  decide +kernel
theorem kg_4168_19 : IPChk.allR (Pts.glueIB K4168.lits KW_4168) 19 3 = true := by decide +kernel

end B334.E1x.Pts.S707
