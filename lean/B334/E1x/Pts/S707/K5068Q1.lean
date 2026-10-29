import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5068L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5068 of `S707`, parts 43 … 57, re-packed by predicted kernel memory (2.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K5068C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5068_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5068.lits.getD i 0)) 43 4 = true := by
  decide +kernel
theorem kg_5068_43 : IPChk.allR (Pts.glueIB K5068.lits KW_5068) 43 4 = true := by decide +kernel
theorem kb_5068_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5068.lits.getD i 0)) 47 4 = true := by
  decide +kernel
theorem kg_5068_47 : IPChk.allR (Pts.glueIB K5068.lits KW_5068) 47 4 = true := by decide +kernel
theorem kb_5068_51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5068.lits.getD i 0)) 51 4 = true := by
  decide +kernel
theorem kg_5068_51 : IPChk.allR (Pts.glueIB K5068.lits KW_5068) 51 4 = true := by decide +kernel
theorem kb_5068_55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5068.lits.getD i 0)) 55 3 = true := by
  decide +kernel
theorem kg_5068_55 : IPChk.allR (Pts.glueIB K5068.lits KW_5068) 55 3 = true := by decide +kernel

end B334.E1x.Pts.S707
