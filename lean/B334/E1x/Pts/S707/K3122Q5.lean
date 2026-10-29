import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3122L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3122 of `S707`, parts 599 … 634, re-packed by predicted kernel memory (2.01 of 8.19 GB;
stage707_v5; the theorems are v3's `K3122C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3122_599 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3122.lits.getD i 0)) 599 26 = true := by
  decide +kernel
theorem kg_3122_599 : IPChk.allR (Pts.glueIB K3122.lits KW_3122) 599 26 = true := by decide +kernel
theorem kb_3122_625 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3122.lits.getD i 0)) 625 8 = true := by
  decide +kernel
theorem kg_3122_625 : IPChk.allR (Pts.glueIB K3122.lits KW_3122) 625 8 = true := by decide +kernel
theorem kb_3122_633 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3122.lits.getD i 0)) 633 2 = true := by
  decide +kernel
theorem kg_3122_633 : IPChk.allR (Pts.glueIB K3122.lits KW_3122) 633 2 = true := by decide +kernel

end B334.E1x.Pts.S707
