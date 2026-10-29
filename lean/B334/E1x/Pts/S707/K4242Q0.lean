import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4242L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4242 of `S707`, parts 0 … 6, re-packed by predicted kernel memory (2.23 of 8.19 GB;
stage707_v5; the theorems are v3's `K4242C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4242_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4242.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4242_0 : IPChk.allR (Pts.glueIB K4242.lits KW_4242) 0 2 = true := by decide +kernel
theorem kb_4242_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4242.lits.getD i 0)) 2 3 = true := by
  decide +kernel
theorem kg_4242_2 : IPChk.allR (Pts.glueIB K4242.lits KW_4242) 2 3 = true := by decide +kernel
theorem kb_4242_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4242.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_4242_5 : IPChk.allR (Pts.glueIB K4242.lits KW_4242) 5 2 = true := by decide +kernel

end B334.E1x.Pts.S707
