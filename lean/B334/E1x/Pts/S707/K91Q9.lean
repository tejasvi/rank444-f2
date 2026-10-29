import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K91L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 91 of `S707`, parts 981 … 1214, re-packed by predicted kernel memory (6.86 of 8.19 GB;
stage707_v5; the theorems are v3's `K91C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_91_981 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 981 1 = true := by
  decide +kernel
theorem kg_91_981 : IPChk.allR (Pts.glueIB K91.lits KW_91) 981 1 = true := by decide +kernel
theorem kb_91_982 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 982 5 = true := by
  decide +kernel
theorem kg_91_982 : IPChk.allR (Pts.glueIB K91.lits KW_91) 982 5 = true := by decide +kernel
theorem kb_91_987 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 987 5 = true := by
  decide +kernel
theorem kg_91_987 : IPChk.allR (Pts.glueIB K91.lits KW_91) 987 5 = true := by decide +kernel
theorem kb_91_992 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 992 80 = true := by
  decide +kernel
theorem kg_91_992 : IPChk.allR (Pts.glueIB K91.lits KW_91) 992 80 = true := by decide +kernel
theorem kb_91_1072 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 1072 36 = true := by
  decide +kernel
theorem kg_91_1072 : IPChk.allR (Pts.glueIB K91.lits KW_91) 1072 36 = true := by decide +kernel
theorem kb_91_1108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 1108 29 = true := by
  decide +kernel
theorem kg_91_1108 : IPChk.allR (Pts.glueIB K91.lits KW_91) 1108 29 = true := by decide +kernel
theorem kb_91_1137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 1137 17 = true := by
  decide +kernel
theorem kg_91_1137 : IPChk.allR (Pts.glueIB K91.lits KW_91) 1137 17 = true := by decide +kernel
theorem kb_91_1154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 1154 61 = true := by
  decide +kernel
theorem kg_91_1154 : IPChk.allR (Pts.glueIB K91.lits KW_91) 1154 61 = true := by decide +kernel

end B334.E1x.Pts.S707
