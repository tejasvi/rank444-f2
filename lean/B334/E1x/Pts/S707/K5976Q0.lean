import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5976L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5976 of `S707`, parts 0 … 44, re-packed by predicted kernel memory (3.53 of 8.19 GB;
stage707_v5; the theorems are v3's `K5976C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5976_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5976.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_5976_0 : IPChk.allR (Pts.glueIB K5976.lits KW_5976) 0 1 = true := by decide +kernel
theorem kb_5976_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5976.lits.getD i 0)) 1 9 = true := by
  decide +kernel
theorem kg_5976_1 : IPChk.allR (Pts.glueIB K5976.lits KW_5976) 1 9 = true := by decide +kernel
theorem kb_5976_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5976.lits.getD i 0)) 10 17 = true := by
  decide +kernel
theorem kg_5976_10 : IPChk.allR (Pts.glueIB K5976.lits KW_5976) 10 17 = true := by decide +kernel
theorem kb_5976_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5976.lits.getD i 0)) 27 16 = true := by
  decide +kernel
theorem kg_5976_27 : IPChk.allR (Pts.glueIB K5976.lits KW_5976) 27 16 = true := by decide +kernel
theorem kb_5976_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5976.lits.getD i 0)) 43 2 = true := by
  decide +kernel
theorem kg_5976_43 : IPChk.allR (Pts.glueIB K5976.lits KW_5976) 43 2 = true := by decide +kernel

end B334.E1x.Pts.S707
