import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2974L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2974 of `S707`, parts 749 … 799, re-packed by predicted kernel memory (2.22 of 8.19 GB;
stage707_v5; the theorems are v3's `K2974C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2974_749 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 749 7 = true := by
  decide +kernel
theorem kg_2974_749 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 749 7 = true := by decide +kernel
theorem kb_2974_756 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 756 30 = true := by
  decide +kernel
theorem kg_2974_756 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 756 30 = true := by decide +kernel
theorem kb_2974_786 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 786 14 = true := by
  decide +kernel
theorem kg_2974_786 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 786 14 = true := by decide +kernel

end B334.E1x.Pts.S707
