import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K117L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 117 of `S707`, parts 550 … 565, re-packed by predicted kernel memory (2.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K117C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_117_550 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 550 13 = true := by
  decide +kernel
theorem kg_117_550 : IPChk.allR (Pts.glueIB K117.lits KW_117) 550 13 = true := by decide +kernel
theorem kb_117_563 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 563 1 = true := by
  decide +kernel
theorem kg_117_563 : IPChk.allR (Pts.glueIB K117.lits KW_117) 563 1 = true := by decide +kernel
theorem kb_117_564 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 564 1 = true := by
  decide +kernel
theorem kg_117_564 : IPChk.allR (Pts.glueIB K117.lits KW_117) 564 1 = true := by decide +kernel
theorem kb_117_565 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 565 1 = true := by
  decide +kernel
theorem kg_117_565 : IPChk.allR (Pts.glueIB K117.lits KW_117) 565 1 = true := by decide +kernel

end B334.E1x.Pts.S707
