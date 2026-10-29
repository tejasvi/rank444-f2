import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3171L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3171 of `S707`, parts 47 … 102, re-packed by predicted kernel memory (4.10 of 8.19 GB;
stage707_v5; the theorems are v3's `K3171C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3171_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 47 17 = true := by
  decide +kernel
theorem kg_3171_47 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 47 17 = true := by decide +kernel
theorem kb_3171_64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 64 5 = true := by
  decide +kernel
theorem kg_3171_64 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 64 5 = true := by decide +kernel
theorem kb_3171_69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 69 9 = true := by
  decide +kernel
theorem kg_3171_69 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 69 9 = true := by decide +kernel
theorem kb_3171_78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 78 1 = true := by
  decide +kernel
theorem kg_3171_78 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 78 1 = true := by decide +kernel
theorem kb_3171_79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 79 1 = true := by
  decide +kernel
theorem kg_3171_79 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 79 1 = true := by decide +kernel
theorem kb_3171_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3171.lits.getD i 0)) 80 23 = true := by
  decide +kernel
theorem kg_3171_80 : IPChk.allR (Pts.glueIB K3171.lits KW_3171) 80 23 = true := by decide +kernel

end B334.E1x.Pts.S707
