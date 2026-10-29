import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1349L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1349 of `S707`, parts 2006 … 2116, re-packed by predicted kernel memory (4.96 of 8.19 GB;
stage707_v5; the theorems are v3's `K1349C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1349_2006 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2006 10 = true := by
  decide +kernel
theorem kg_1349_2006 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2006 10 = true := by decide +kernel
theorem kb_1349_2016 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2016 30 = true := by
  decide +kernel
theorem kg_1349_2016 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2016 30 = true := by decide +kernel
theorem kb_1349_2046 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2046 26 = true := by
  decide +kernel
theorem kg_1349_2046 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2046 26 = true := by decide +kernel
theorem kb_1349_2072 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2072 21 = true := by
  decide +kernel
theorem kg_1349_2072 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2072 21 = true := by decide +kernel
theorem kb_1349_2093 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2093 10 = true := by
  decide +kernel
theorem kg_1349_2093 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2093 10 = true := by decide +kernel
theorem kb_1349_2103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 2103 14 = true := by
  decide +kernel
theorem kg_1349_2103 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 2103 14 = true := by decide +kernel

end B334.E1x.Pts.S707
