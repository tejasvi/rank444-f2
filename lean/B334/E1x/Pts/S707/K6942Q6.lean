import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6942L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6942 of `S707`, parts 584 … 671, re-packed by predicted kernel memory (4.81 of 8.19 GB;
stage707_v5; the theorems are v3's `K6942C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6942_584 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 584 6 = true := by
  decide +kernel
theorem kg_6942_584 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 584 6 = true := by decide +kernel
theorem kb_6942_590 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 590 7 = true := by
  decide +kernel
theorem kg_6942_590 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 590 7 = true := by decide +kernel
theorem kb_6942_597 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 597 12 = true := by
  decide +kernel
theorem kg_6942_597 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 597 12 = true := by decide +kernel
theorem kb_6942_609 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 609 36 = true := by
  decide +kernel
theorem kg_6942_609 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 609 36 = true := by decide +kernel
theorem kb_6942_645 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 645 12 = true := by
  decide +kernel
theorem kg_6942_645 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 645 12 = true := by decide +kernel
theorem kb_6942_657 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 657 15 = true := by
  decide +kernel
theorem kg_6942_657 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 657 15 = true := by decide +kernel

end B334.E1x.Pts.S707
