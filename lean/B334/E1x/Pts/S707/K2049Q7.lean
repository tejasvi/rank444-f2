import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2049L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2049 of `S707`, parts 735 … 746, re-packed by predicted kernel memory (1.32 of 8.19 GB;
stage707_v5; the theorems are v3's `K2049C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2049_735 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2049.lits.getD i 0)) 735 6 = true := by
  decide +kernel
theorem kg_2049_735 : IPChk.allR (Pts.glueIB K2049.lits KW_2049) 735 6 = true := by decide +kernel
theorem kb_2049_741 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2049.lits.getD i 0)) 741 6 = true := by
  decide +kernel
theorem kg_2049_741 : IPChk.allR (Pts.glueIB K2049.lits KW_2049) 741 6 = true := by decide +kernel

end B334.E1x.Pts.S707
