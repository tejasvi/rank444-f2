import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1561L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1561 of `S707`, parts 128 … 179, re-packed by predicted kernel memory (4.36 of 8.19 GB;
stage707_v5; the theorems are v3's `K1561C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1561_128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 128 24 = true := by
  decide +kernel
theorem kg_1561_128 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 128 24 = true := by decide +kernel
theorem kb_1561_152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 152 17 = true := by
  decide +kernel
theorem kg_1561_152 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 152 17 = true := by decide +kernel
theorem kb_1561_169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 169 2 = true := by
  decide +kernel
theorem kg_1561_169 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 169 2 = true := by decide +kernel
theorem kb_1561_171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 171 2 = true := by
  decide +kernel
theorem kg_1561_171 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 171 2 = true := by decide +kernel
theorem kb_1561_173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 173 3 = true := by
  decide +kernel
theorem kg_1561_173 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 173 3 = true := by decide +kernel
theorem kb_1561_176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1561.lits.getD i 0)) 176 4 = true := by
  decide +kernel
theorem kg_1561_176 : IPChk.allR (Pts.glueIB K1561.lits KW_1561) 176 4 = true := by decide +kernel

end B334.E1x.Pts.S707
