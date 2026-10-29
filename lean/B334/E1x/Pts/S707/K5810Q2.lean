import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5810L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5810 of `S707`, parts 47 … 53, re-packed by predicted kernel memory (2.72 of 8.19 GB;
stage707_v5; the theorems are v3's `K5810C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5810_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5810.lits.getD i 0)) 47 2 = true := by
  decide +kernel
theorem kg_5810_47 : IPChk.allR (Pts.glueIB K5810.lits KW_5810) 47 2 = true := by decide +kernel
theorem kb_5810_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5810.lits.getD i 0)) 49 1 = true := by
  decide +kernel
theorem kg_5810_49 : IPChk.allR (Pts.glueIB K5810.lits KW_5810) 49 1 = true := by decide +kernel
theorem kb_5810_50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5810.lits.getD i 0)) 50 2 = true := by
  decide +kernel
theorem kg_5810_50 : IPChk.allR (Pts.glueIB K5810.lits KW_5810) 50 2 = true := by decide +kernel
theorem kb_5810_52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5810.lits.getD i 0)) 52 2 = true := by
  decide +kernel
theorem kg_5810_52 : IPChk.allR (Pts.glueIB K5810.lits KW_5810) 52 2 = true := by decide +kernel

end B334.E1x.Pts.S707
