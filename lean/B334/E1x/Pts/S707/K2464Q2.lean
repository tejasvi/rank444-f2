import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2464L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2464 of `S707`, parts 299 … 426, re-packed by predicted kernel memory (3.80 of 8.19 GB;
stage707_v5; the theorems are v3's `K2464C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2464_299 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 299 18 = true := by
  decide +kernel
theorem kg_2464_299 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 299 18 = true := by decide +kernel
theorem kb_2464_317 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 317 2 = true := by
  decide +kernel
theorem kg_2464_317 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 317 2 = true := by decide +kernel
theorem kb_2464_319 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 319 31 = true := by
  decide +kernel
theorem kg_2464_319 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 319 31 = true := by decide +kernel
theorem kb_2464_350 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 350 30 = true := by
  decide +kernel
theorem kg_2464_350 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 350 30 = true := by decide +kernel
theorem kb_2464_380 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 380 21 = true := by
  decide +kernel
theorem kg_2464_380 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 380 21 = true := by decide +kernel
theorem kb_2464_401 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 401 26 = true := by
  decide +kernel
theorem kg_2464_401 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 401 26 = true := by decide +kernel

end B334.E1x.Pts.S707
