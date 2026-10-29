import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4205L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4205 of `S707`, parts 0 … 15, re-packed by predicted kernel memory (3.65 of 8.19 GB;
stage707_v5; the theorems are v3's `K4205C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4205_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4205.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_4205_0 : IPChk.allR (Pts.glueIB K4205.lits KW_4205) 0 4 = true := by decide +kernel
theorem kb_4205_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4205.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_4205_4 : IPChk.allR (Pts.glueIB K4205.lits KW_4205) 4 1 = true := by decide +kernel
theorem kb_4205_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4205.lits.getD i 0)) 5 7 = true := by
  decide +kernel
theorem kg_4205_5 : IPChk.allR (Pts.glueIB K4205.lits KW_4205) 5 7 = true := by decide +kernel
theorem kb_4205_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4205.lits.getD i 0)) 12 3 = true := by
  decide +kernel
theorem kg_4205_12 : IPChk.allR (Pts.glueIB K4205.lits KW_4205) 12 3 = true := by decide +kernel
theorem kb_4205_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4205.lits.getD i 0)) 15 1 = true := by
  decide +kernel
theorem kg_4205_15 : IPChk.allR (Pts.glueIB K4205.lits KW_4205) 15 1 = true := by decide +kernel

end B334.E1x.Pts.S707
