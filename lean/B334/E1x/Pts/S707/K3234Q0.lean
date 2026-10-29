import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3234L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3234 of `S707`, parts 0 … 6, re-packed by predicted kernel memory (2.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K3234C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3234_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3234.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_3234_0 : IPChk.allR (Pts.glueIB K3234.lits KW_3234) 0 5 = true := by decide +kernel
theorem kb_3234_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3234.lits.getD i 0)) 5 1 = true := by
  decide +kernel
theorem kg_3234_5 : IPChk.allR (Pts.glueIB K3234.lits KW_3234) 5 1 = true := by decide +kernel
theorem kb_3234_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3234.lits.getD i 0)) 6 1 = true := by
  decide +kernel
theorem kg_3234_6 : IPChk.allR (Pts.glueIB K3234.lits KW_3234) 6 1 = true := by decide +kernel

end B334.E1x.Pts.S707
