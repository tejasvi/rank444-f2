import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1259L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1259 of `S707`, parts 539 … 541, re-packed by predicted kernel memory (1.05 of 8.19 GB;
stage707_v5; the theorems are v3's `K1259C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1259_539 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 539 2 = true := by
  decide +kernel
theorem kg_1259_539 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 539 2 = true := by decide +kernel
theorem kb_1259_541 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 541 1 = true := by
  decide +kernel
theorem kg_1259_541 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 541 1 = true := by decide +kernel

end B334.E1x.Pts.S707
