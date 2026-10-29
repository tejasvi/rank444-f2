import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2664L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2664 of `S707`, parts 0 … 114, re-packed by predicted kernel memory (3.16 of 8.19 GB;
stage707_v5; the theorems are v3's `K2664C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2664_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2664.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_2664_0 : IPChk.allR (Pts.glueIB K2664.lits KW_2664) 0 1 = true := by decide +kernel
theorem kb_2664_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2664.lits.getD i 0)) 1 11 = true := by
  decide +kernel
theorem kg_2664_1 : IPChk.allR (Pts.glueIB K2664.lits KW_2664) 1 11 = true := by decide +kernel
theorem kb_2664_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2664.lits.getD i 0)) 12 56 = true := by
  decide +kernel
theorem kg_2664_12 : IPChk.allR (Pts.glueIB K2664.lits KW_2664) 12 56 = true := by decide +kernel
theorem kb_2664_68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2664.lits.getD i 0)) 68 47 = true := by
  decide +kernel
theorem kg_2664_68 : IPChk.allR (Pts.glueIB K2664.lits KW_2664) 68 47 = true := by decide +kernel

end B334.E1x.Pts.S707
