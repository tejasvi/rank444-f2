import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1220L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1220 of `S707`, parts 180 … 358, re-packed by predicted kernel memory (4.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K1220C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1220_180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 180 14 = true := by
  decide +kernel
theorem kg_1220_180 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 180 14 = true := by decide +kernel
theorem kb_1220_194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 194 29 = true := by
  decide +kernel
theorem kg_1220_194 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 194 29 = true := by decide +kernel
theorem kb_1220_223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 223 46 = true := by
  decide +kernel
theorem kg_1220_223 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 223 46 = true := by decide +kernel
theorem kb_1220_269 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 269 15 = true := by
  decide +kernel
theorem kg_1220_269 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 269 15 = true := by decide +kernel
theorem kb_1220_284 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 284 17 = true := by
  decide +kernel
theorem kg_1220_284 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 284 17 = true := by decide +kernel
theorem kb_1220_301 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 301 58 = true := by
  decide +kernel
theorem kg_1220_301 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 301 58 = true := by decide +kernel

end B334.E1x.Pts.S707
