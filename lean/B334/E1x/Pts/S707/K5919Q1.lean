import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5919L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5919 of `S707`, parts 38 … 48, re-packed by predicted kernel memory (4.12 of 8.19 GB;
stage707_v5; the theorems are v3's `K5919C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5919_38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5919.lits.getD i 0)) 38 1 = true := by
  decide +kernel
theorem kg_5919_38 : IPChk.allR (Pts.glueIB K5919.lits KW_5919) 38 1 = true := by decide +kernel
theorem kb_5919_39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5919.lits.getD i 0)) 39 2 = true := by
  decide +kernel
theorem kg_5919_39 : IPChk.allR (Pts.glueIB K5919.lits KW_5919) 39 2 = true := by decide +kernel
theorem kb_5919_41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5919.lits.getD i 0)) 41 2 = true := by
  decide +kernel
theorem kg_5919_41 : IPChk.allR (Pts.glueIB K5919.lits KW_5919) 41 2 = true := by decide +kernel
theorem kb_5919_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5919.lits.getD i 0)) 43 3 = true := by
  decide +kernel
theorem kg_5919_43 : IPChk.allR (Pts.glueIB K5919.lits KW_5919) 43 3 = true := by decide +kernel
theorem kb_5919_46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5919.lits.getD i 0)) 46 3 = true := by
  decide +kernel
theorem kg_5919_46 : IPChk.allR (Pts.glueIB K5919.lits KW_5919) 46 3 = true := by decide +kernel

end B334.E1x.Pts.S707
