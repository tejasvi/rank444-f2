import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1459L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1459 of `S707`, parts 824 … 836, re-packed by predicted kernel memory (1.60 of 8.19 GB;
stage707_v5; the theorems are v3's `K1459C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1459_824 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 824 4 = true := by
  decide +kernel
theorem kg_1459_824 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 824 4 = true := by decide +kernel
theorem kb_1459_828 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 828 9 = true := by
  decide +kernel
theorem kg_1459_828 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 828 9 = true := by decide +kernel

end B334.E1x.Pts.S707
