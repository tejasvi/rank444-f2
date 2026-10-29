import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K985L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 985 of `S707`, parts 639 … 685, re-packed by predicted kernel memory (6.29 of 8.19 GB;
stage707_v5; the theorems are v3's `K985C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_985_639 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 639 1 = true := by
  decide +kernel
theorem kg_985_639 : IPChk.allR (Pts.glueIB K985.lits KW_985) 639 1 = true := by decide +kernel
theorem kb_985_640 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 640 2 = true := by
  decide +kernel
theorem kg_985_640 : IPChk.allR (Pts.glueIB K985.lits KW_985) 640 2 = true := by decide +kernel
theorem kb_985_642 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 642 1 = true := by
  decide +kernel
theorem kg_985_642 : IPChk.allR (Pts.glueIB K985.lits KW_985) 642 1 = true := by decide +kernel
theorem kb_985_643 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 643 1 = true := by
  decide +kernel
theorem kg_985_643 : IPChk.allR (Pts.glueIB K985.lits KW_985) 643 1 = true := by decide +kernel
theorem kb_985_644 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 644 13 = true := by
  decide +kernel
theorem kg_985_644 : IPChk.allR (Pts.glueIB K985.lits KW_985) 644 13 = true := by decide +kernel
theorem kb_985_657 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 657 7 = true := by
  decide +kernel
theorem kg_985_657 : IPChk.allR (Pts.glueIB K985.lits KW_985) 657 7 = true := by decide +kernel
theorem kb_985_664 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 664 12 = true := by
  decide +kernel
theorem kg_985_664 : IPChk.allR (Pts.glueIB K985.lits KW_985) 664 12 = true := by decide +kernel
theorem kb_985_676 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 676 10 = true := by
  decide +kernel
theorem kg_985_676 : IPChk.allR (Pts.glueIB K985.lits KW_985) 676 10 = true := by decide +kernel

end B334.E1x.Pts.S707
