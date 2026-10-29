import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5406L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5406 of `S707`, parts 310 … 333, re-packed by predicted kernel memory (2.20 of 8.19 GB;
stage707_v5; the theorems are v3's `K5406C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5406_310 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5406.lits.getD i 0)) 310 4 = true := by
  decide +kernel
theorem kg_5406_310 : IPChk.allR (Pts.glueIB K5406.lits KW_5406) 310 4 = true := by decide +kernel
theorem kb_5406_314 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5406.lits.getD i 0)) 314 9 = true := by
  decide +kernel
theorem kg_5406_314 : IPChk.allR (Pts.glueIB K5406.lits KW_5406) 314 9 = true := by decide +kernel
theorem kb_5406_323 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5406.lits.getD i 0)) 323 8 = true := by
  decide +kernel
theorem kg_5406_323 : IPChk.allR (Pts.glueIB K5406.lits KW_5406) 323 8 = true := by decide +kernel
theorem kb_5406_331 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5406.lits.getD i 0)) 331 3 = true := by
  decide +kernel
theorem kg_5406_331 : IPChk.allR (Pts.glueIB K5406.lits KW_5406) 331 3 = true := by decide +kernel

end B334.E1x.Pts.S707
