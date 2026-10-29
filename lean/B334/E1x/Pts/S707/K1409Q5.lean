import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1409L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1409 of `S707`, parts 798 … 1064, re-packed by predicted kernel memory (2.84 of 8.19 GB;
stage707_v5; the theorems are v3's `K1409C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1409_798 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 798 91 = true := by
  decide +kernel
theorem kg_1409_798 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 798 91 = true := by decide +kernel
theorem kb_1409_889 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 889 83 = true := by
  decide +kernel
theorem kg_1409_889 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 889 83 = true := by decide +kernel
theorem kb_1409_972 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 972 56 = true := by
  decide +kernel
theorem kg_1409_972 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 972 56 = true := by decide +kernel
theorem kb_1409_1028 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 1028 37 = true := by
  decide +kernel
theorem kg_1409_1028 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 1028 37 = true := by decide +kernel

end B334.E1x.Pts.S707
