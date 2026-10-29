import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K975L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 975 of `S707`, parts 1197 … 1205, re-packed by predicted kernel memory (3.91 of 8.19 GB;
stage707_v5; the theorems are v3's `K975C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_975_1197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1197 2 = true := by
  decide +kernel
theorem kg_975_1197 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1197 2 = true := by decide +kernel
theorem kb_975_1199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1199 2 = true := by
  decide +kernel
theorem kg_975_1199 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1199 2 = true := by decide +kernel
theorem kb_975_1201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1201 1 = true := by
  decide +kernel
theorem kg_975_1201 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1201 1 = true := by decide +kernel
theorem kb_975_1202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1202 1 = true := by
  decide +kernel
theorem kg_975_1202 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1202 1 = true := by decide +kernel
theorem kb_975_1203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1203 2 = true := by
  decide +kernel
theorem kg_975_1203 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1203 2 = true := by decide +kernel
theorem kb_975_1205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 1205 1 = true := by
  decide +kernel
theorem kg_975_1205 : IPChk.allR (Pts.glueIB K975.lits KW_975) 1205 1 = true := by decide +kernel

end B334.E1x.Pts.S707
