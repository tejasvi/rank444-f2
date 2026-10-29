import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4542L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4542 of `S707`, parts 100 … 108, re-packed by predicted kernel memory (3.30 of 8.19 GB;
stage707_v5; the theorems are v3's `K4542C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4542_100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4542.lits.getD i 0)) 100 2 = true := by
  decide +kernel
theorem kg_4542_100 : IPChk.allR (Pts.glueIB K4542.lits KW_4542) 100 2 = true := by decide +kernel
theorem kb_4542_102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4542.lits.getD i 0)) 102 2 = true := by
  decide +kernel
theorem kg_4542_102 : IPChk.allR (Pts.glueIB K4542.lits KW_4542) 102 2 = true := by decide +kernel
theorem kb_4542_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4542.lits.getD i 0)) 104 1 = true := by
  decide +kernel
theorem kg_4542_104 : IPChk.allR (Pts.glueIB K4542.lits KW_4542) 104 1 = true := by decide +kernel
theorem kb_4542_105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4542.lits.getD i 0)) 105 2 = true := by
  decide +kernel
theorem kg_4542_105 : IPChk.allR (Pts.glueIB K4542.lits KW_4542) 105 2 = true := by decide +kernel
theorem kb_4542_107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4542.lits.getD i 0)) 107 2 = true := by
  decide +kernel
theorem kg_4542_107 : IPChk.allR (Pts.glueIB K4542.lits KW_4542) 107 2 = true := by decide +kernel

end B334.E1x.Pts.S707
