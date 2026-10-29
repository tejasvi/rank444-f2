import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5621L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5621 of `S707`, parts 0 … 24, re-packed by predicted kernel memory (2.20 of 8.19 GB;
stage707_v5; the theorems are v3's `K5621C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5621_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5621.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_5621_0 : IPChk.allR (Pts.glueIB K5621.lits KW_5621) 0 3 = true := by decide +kernel
theorem kb_5621_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5621.lits.getD i 0)) 3 12 = true := by
  decide +kernel
theorem kg_5621_3 : IPChk.allR (Pts.glueIB K5621.lits KW_5621) 3 12 = true := by decide +kernel
theorem kb_5621_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5621.lits.getD i 0)) 15 10 = true := by
  decide +kernel
theorem kg_5621_15 : IPChk.allR (Pts.glueIB K5621.lits KW_5621) 15 10 = true := by decide +kernel

end B334.E1x.Pts.S707
