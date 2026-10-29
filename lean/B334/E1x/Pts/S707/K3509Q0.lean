import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3509L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3509 of `S707`, parts 0 … 45, re-packed by predicted kernel memory (3.77 of 8.19 GB;
stage707_v5; the theorems are v3's `K3509C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3509_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3509_0 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 0 2 = true := by decide +kernel
theorem kb_3509_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 2 22 = true := by
  decide +kernel
theorem kg_3509_2 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 2 22 = true := by decide +kernel
theorem kb_3509_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 24 1 = true := by
  decide +kernel
theorem kg_3509_24 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 24 1 = true := by decide +kernel
theorem kb_3509_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 25 2 = true := by
  decide +kernel
theorem kg_3509_25 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 25 2 = true := by decide +kernel
theorem kb_3509_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 27 18 = true := by
  decide +kernel
theorem kg_3509_27 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 27 18 = true := by decide +kernel
theorem kb_3509_45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3509.lits.getD i 0)) 45 1 = true := by
  decide +kernel
theorem kg_3509_45 : IPChk.allR (Pts.glueIB K3509.lits KW_3509) 45 1 = true := by decide +kernel

end B334.E1x.Pts.S707
