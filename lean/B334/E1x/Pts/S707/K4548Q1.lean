import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4548L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4548 of `S707`, parts 35 … 59, re-packed by predicted kernel memory (5.30 of 8.19 GB;
stage707_v5; the theorems are v3's `K4548C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4548_35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 35 1 = true := by
  decide +kernel
theorem kg_4548_35 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 35 1 = true := by decide +kernel
theorem kb_4548_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 36 10 = true := by
  decide +kernel
theorem kg_4548_36 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 36 10 = true := by decide +kernel
theorem kb_4548_46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 46 8 = true := by
  decide +kernel
theorem kg_4548_46 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 46 8 = true := by decide +kernel
theorem kb_4548_54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 54 1 = true := by
  decide +kernel
theorem kg_4548_54 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 54 1 = true := by decide +kernel
theorem kb_4548_55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 55 2 = true := by
  decide +kernel
theorem kg_4548_55 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 55 2 = true := by decide +kernel
theorem kb_4548_57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 57 2 = true := by
  decide +kernel
theorem kg_4548_57 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 57 2 = true := by decide +kernel
theorem kb_4548_59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4548.lits.getD i 0)) 59 1 = true := by
  decide +kernel
theorem kg_4548_59 : IPChk.allR (Pts.glueIB K4548.lits KW_4548) 59 1 = true := by decide +kernel

end B334.E1x.Pts.S707
