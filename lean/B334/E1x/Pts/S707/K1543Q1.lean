import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1543L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1543 of `S707`, parts 71 … 120, re-packed by predicted kernel memory (3.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K1543C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1543_71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1543.lits.getD i 0)) 71 19 = true := by
  decide +kernel
theorem kg_1543_71 : IPChk.allR (Pts.glueIB K1543.lits KW_1543) 71 19 = true := by decide +kernel
theorem kb_1543_90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1543.lits.getD i 0)) 90 2 = true := by
  decide +kernel
theorem kg_1543_90 : IPChk.allR (Pts.glueIB K1543.lits KW_1543) 90 2 = true := by decide +kernel
theorem kb_1543_92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1543.lits.getD i 0)) 92 27 = true := by
  decide +kernel
theorem kg_1543_92 : IPChk.allR (Pts.glueIB K1543.lits KW_1543) 92 27 = true := by decide +kernel
theorem kb_1543_119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1543.lits.getD i 0)) 119 2 = true := by
  decide +kernel
theorem kg_1543_119 : IPChk.allR (Pts.glueIB K1543.lits KW_1543) 119 2 = true := by decide +kernel

end B334.E1x.Pts.S707
