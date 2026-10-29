import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2567L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2567 of `S707`, parts 600 … 684, re-packed by predicted kernel memory (3.92 of 8.19 GB;
stage707_v5; the theorems are v3's `K2567C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2567_600 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2567.lits.getD i 0)) 600 30 = true := by
  decide +kernel
theorem kg_2567_600 : IPChk.allR (Pts.glueIB K2567.lits KW_2567) 600 30 = true := by decide +kernel
theorem kb_2567_630 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2567.lits.getD i 0)) 630 8 = true := by
  decide +kernel
theorem kg_2567_630 : IPChk.allR (Pts.glueIB K2567.lits KW_2567) 630 8 = true := by decide +kernel
theorem kb_2567_638 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2567.lits.getD i 0)) 638 24 = true := by
  decide +kernel
theorem kg_2567_638 : IPChk.allR (Pts.glueIB K2567.lits KW_2567) 638 24 = true := by decide +kernel
theorem kb_2567_662 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2567.lits.getD i 0)) 662 6 = true := by
  decide +kernel
theorem kg_2567_662 : IPChk.allR (Pts.glueIB K2567.lits KW_2567) 662 6 = true := by decide +kernel
theorem kb_2567_668 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2567.lits.getD i 0)) 668 17 = true := by
  decide +kernel
theorem kg_2567_668 : IPChk.allR (Pts.glueIB K2567.lits KW_2567) 668 17 = true := by decide +kernel

end B334.E1x.Pts.S707
