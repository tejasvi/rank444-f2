import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3025L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3025 of `S707`, parts 865 … 900, re-packed by predicted kernel memory (4.08 of 8.19 GB;
stage707_v5; the theorems are v3's `K3025C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3025_865 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 865 4 = true := by
  decide +kernel
theorem kg_3025_865 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 865 4 = true := by decide +kernel
theorem kb_3025_869 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 869 4 = true := by
  decide +kernel
theorem kg_3025_869 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 869 4 = true := by decide +kernel
theorem kb_3025_873 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 873 2 = true := by
  decide +kernel
theorem kg_3025_873 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 873 2 = true := by decide +kernel
theorem kb_3025_875 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 875 12 = true := by
  decide +kernel
theorem kg_3025_875 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 875 12 = true := by decide +kernel
theorem kb_3025_887 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 887 10 = true := by
  decide +kernel
theorem kg_3025_887 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 887 10 = true := by decide +kernel
theorem kb_3025_897 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 897 4 = true := by
  decide +kernel
theorem kg_3025_897 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 897 4 = true := by decide +kernel

end B334.E1x.Pts.S707
