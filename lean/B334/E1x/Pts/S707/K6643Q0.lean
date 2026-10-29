import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6643L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6643 of `S707`, parts 0 … 18, re-packed by predicted kernel memory (3.74 of 8.19 GB;
stage707_v5; the theorems are v3's `K6643C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6643_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6643.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_6643_0 : IPChk.allR (Pts.glueIB K6643.lits KW_6643) 0 5 = true := by decide +kernel
theorem kb_6643_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6643.lits.getD i 0)) 5 1 = true := by
  decide +kernel
theorem kg_6643_5 : IPChk.allR (Pts.glueIB K6643.lits KW_6643) 5 1 = true := by decide +kernel
theorem kb_6643_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6643.lits.getD i 0)) 6 8 = true := by
  decide +kernel
theorem kg_6643_6 : IPChk.allR (Pts.glueIB K6643.lits KW_6643) 6 8 = true := by decide +kernel
theorem kb_6643_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6643.lits.getD i 0)) 14 3 = true := by
  decide +kernel
theorem kg_6643_14 : IPChk.allR (Pts.glueIB K6643.lits KW_6643) 14 3 = true := by decide +kernel
theorem kb_6643_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6643.lits.getD i 0)) 17 2 = true := by
  decide +kernel
theorem kg_6643_17 : IPChk.allR (Pts.glueIB K6643.lits KW_6643) 17 2 = true := by decide +kernel

end B334.E1x.Pts.S707
