import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K975L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 975 of `S707`, parts 40 … 55, re-packed by predicted kernel memory (7.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K975C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_975_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 40 1 = true := by
  decide +kernel
theorem kg_975_40 : IPChk.allR (Pts.glueIB K975.lits KW_975) 40 1 = true := by decide +kernel
theorem kb_975_41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 41 2 = true := by
  decide +kernel
theorem kg_975_41 : IPChk.allR (Pts.glueIB K975.lits KW_975) 41 2 = true := by decide +kernel
theorem kb_975_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 43 1 = true := by
  decide +kernel
theorem kg_975_43 : IPChk.allR (Pts.glueIB K975.lits KW_975) 43 1 = true := by decide +kernel
theorem kb_975_44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 44 1 = true := by
  decide +kernel
theorem kg_975_44 : IPChk.allR (Pts.glueIB K975.lits KW_975) 44 1 = true := by decide +kernel
theorem kb_975_45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 45 2 = true := by
  decide +kernel
theorem kg_975_45 : IPChk.allR (Pts.glueIB K975.lits KW_975) 45 2 = true := by decide +kernel
theorem kb_975_47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 47 1 = true := by
  decide +kernel
theorem kg_975_47 : IPChk.allR (Pts.glueIB K975.lits KW_975) 47 1 = true := by decide +kernel
theorem kb_975_48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 48 5 = true := by
  decide +kernel
theorem kg_975_48 : IPChk.allR (Pts.glueIB K975.lits KW_975) 48 5 = true := by decide +kernel
theorem kb_975_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 53 2 = true := by
  decide +kernel
theorem kg_975_53 : IPChk.allR (Pts.glueIB K975.lits KW_975) 53 2 = true := by decide +kernel
theorem kb_975_55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 55 1 = true := by
  decide +kernel
theorem kg_975_55 : IPChk.allR (Pts.glueIB K975.lits KW_975) 55 1 = true := by decide +kernel

end B334.E1x.Pts.S707
