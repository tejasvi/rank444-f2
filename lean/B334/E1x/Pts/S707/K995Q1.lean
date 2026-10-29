import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K995L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 995 of `S707`, parts 182 … 219, re-packed by predicted kernel memory (1.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K995C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_995_182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 182 7 = true := by
  decide +kernel
theorem kg_995_182 : IPChk.allR (Pts.glueIB K995.lits KW_995) 182 7 = true := by decide +kernel
theorem kb_995_189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 189 31 = true := by
  decide +kernel
theorem kg_995_189 : IPChk.allR (Pts.glueIB K995.lits KW_995) 189 31 = true := by decide +kernel

end B334.E1x.Pts.S707
