import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K742L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 742 of `S707`, parts 0 … 10, re-packed by predicted kernel memory (1.83 of 8.19 GB;
stage707_v5; the theorems are v3's `K742C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_742_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K742.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_742_0 : IPChk.allR (Pts.glueIB K742.lits KW_742) 0 2 = true := by decide +kernel
theorem kb_742_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K742.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_742_2 : IPChk.allR (Pts.glueIB K742.lits KW_742) 2 6 = true := by decide +kernel
theorem kb_742_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K742.lits.getD i 0)) 8 3 = true := by
  decide +kernel
theorem kg_742_8 : IPChk.allR (Pts.glueIB K742.lits KW_742) 8 3 = true := by decide +kernel

end B334.E1x.Pts.S707
