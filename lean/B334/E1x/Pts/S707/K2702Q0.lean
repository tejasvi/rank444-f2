import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2702L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2702 of `S707`, parts 0 … 74, re-packed by predicted kernel memory (5.48 of 8.19 GB;
stage707_v5; the theorems are v3's `K2702C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2702_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_2702_0 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 0 5 = true := by decide +kernel
theorem kb_2702_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 5 5 = true := by
  decide +kernel
theorem kg_2702_5 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 5 5 = true := by decide +kernel
theorem kb_2702_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 10 17 = true := by
  decide +kernel
theorem kg_2702_10 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 10 17 = true := by decide +kernel
theorem kb_2702_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 27 4 = true := by
  decide +kernel
theorem kg_2702_27 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 27 4 = true := by decide +kernel
theorem kb_2702_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 31 4 = true := by
  decide +kernel
theorem kg_2702_31 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 31 4 = true := by decide +kernel
theorem kb_2702_35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 35 12 = true := by
  decide +kernel
theorem kg_2702_35 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 35 12 = true := by decide +kernel
theorem kb_2702_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2702.lits.getD i 0)) 47 28 = true := by
  decide +kernel
theorem kg_2702_47 : IPChk.allR (Pts.glueIB K2702.lits KW_2702) 47 28 = true := by decide +kernel

end B334.E1x.Pts.S707
