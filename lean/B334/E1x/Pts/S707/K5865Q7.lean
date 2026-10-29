import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5865L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5865 of `S707`, parts 284 … 297, re-packed by predicted kernel memory (3.79 of 8.19 GB;
stage707_v5; the theorems are v3's `K5865C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5865_284 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5865.lits.getD i 0)) 284 2 = true := by
  decide +kernel
theorem kg_5865_284 : IPChk.allR (Pts.glueIB K5865.lits KW_5865) 284 2 = true := by decide +kernel
theorem kb_5865_286 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5865.lits.getD i 0)) 286 2 = true := by
  decide +kernel
theorem kg_5865_286 : IPChk.allR (Pts.glueIB K5865.lits KW_5865) 286 2 = true := by decide +kernel
theorem kb_5865_288 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5865.lits.getD i 0)) 288 2 = true := by
  decide +kernel
theorem kg_5865_288 : IPChk.allR (Pts.glueIB K5865.lits KW_5865) 288 2 = true := by decide +kernel
theorem kb_5865_290 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5865.lits.getD i 0)) 290 3 = true := by
  decide +kernel
theorem kg_5865_290 : IPChk.allR (Pts.glueIB K5865.lits KW_5865) 290 3 = true := by decide +kernel
theorem kb_5865_293 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5865.lits.getD i 0)) 293 5 = true := by
  decide +kernel
theorem kg_5865_293 : IPChk.allR (Pts.glueIB K5865.lits KW_5865) 293 5 = true := by decide +kernel

end B334.E1x.Pts.S707
