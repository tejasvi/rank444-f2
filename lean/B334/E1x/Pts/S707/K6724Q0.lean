import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6724L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6724 of `S707`, parts 0 … 7, re-packed by predicted kernel memory (2.47 of 8.19 GB;
stage707_v5; the theorems are v3's `K6724C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6724_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6724.lits.getD i 0)) 0 4 = true := by
  decide +kernel
theorem kg_6724_0 : IPChk.allR (Pts.glueIB K6724.lits KW_6724) 0 4 = true := by decide +kernel
theorem kb_6724_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6724.lits.getD i 0)) 4 2 = true := by
  decide +kernel
theorem kg_6724_4 : IPChk.allR (Pts.glueIB K6724.lits KW_6724) 4 2 = true := by decide +kernel
theorem kb_6724_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6724.lits.getD i 0)) 6 1 = true := by
  decide +kernel
theorem kg_6724_6 : IPChk.allR (Pts.glueIB K6724.lits KW_6724) 6 1 = true := by decide +kernel
theorem kb_6724_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6724.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_6724_7 : IPChk.allR (Pts.glueIB K6724.lits KW_6724) 7 1 = true := by decide +kernel

end B334.E1x.Pts.S707
