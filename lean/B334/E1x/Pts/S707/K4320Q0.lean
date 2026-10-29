import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4320L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4320 of `S707`, parts 0 … 8, re-packed by predicted kernel memory (3.85 of 8.19 GB;
stage707_v5; the theorems are v3's `K4320C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4320_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4320.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4320_0 : IPChk.allR (Pts.glueIB K4320.lits KW_4320) 0 2 = true := by decide +kernel
theorem kb_4320_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4320.lits.getD i 0)) 2 2 = true := by
  decide +kernel
theorem kg_4320_2 : IPChk.allR (Pts.glueIB K4320.lits KW_4320) 2 2 = true := by decide +kernel
theorem kb_4320_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4320.lits.getD i 0)) 4 1 = true := by
  decide +kernel
theorem kg_4320_4 : IPChk.allR (Pts.glueIB K4320.lits KW_4320) 4 1 = true := by decide +kernel
theorem kb_4320_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4320.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_4320_5 : IPChk.allR (Pts.glueIB K4320.lits KW_4320) 5 2 = true := by decide +kernel
theorem kb_4320_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4320.lits.getD i 0)) 7 2 = true := by
  decide +kernel
theorem kg_4320_7 : IPChk.allR (Pts.glueIB K4320.lits KW_4320) 7 2 = true := by decide +kernel

end B334.E1x.Pts.S707
