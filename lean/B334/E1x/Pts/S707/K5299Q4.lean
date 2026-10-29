import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5299L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5299 of `S707`, parts 182 … 185, re-packed by predicted kernel memory (1.50 of 8.19 GB;
stage707_v5; the theorems are v3's `K5299C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5299_182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5299.lits.getD i 0)) 182 1 = true := by
  decide +kernel
theorem kg_5299_182 : IPChk.allR (Pts.glueIB K5299.lits KW_5299) 182 1 = true := by decide +kernel
theorem kb_5299_183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5299.lits.getD i 0)) 183 1 = true := by
  decide +kernel
theorem kg_5299_183 : IPChk.allR (Pts.glueIB K5299.lits KW_5299) 183 1 = true := by decide +kernel
theorem kb_5299_184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5299.lits.getD i 0)) 184 2 = true := by
  decide +kernel
theorem kg_5299_184 : IPChk.allR (Pts.glueIB K5299.lits KW_5299) 184 2 = true := by decide +kernel

end B334.E1x.Pts.S707
