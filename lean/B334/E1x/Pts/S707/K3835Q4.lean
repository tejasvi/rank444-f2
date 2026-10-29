import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3835L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3835 of `S707`, parts 501 … 512, re-packed by predicted kernel memory (1.00 of 8.19 GB;
stage707_v5; the theorems are v3's `K3835C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3835_501 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3835.lits.getD i 0)) 501 9 = true := by
  decide +kernel
theorem kg_3835_501 : IPChk.allR (Pts.glueIB K3835.lits KW_3835) 501 9 = true := by decide +kernel
theorem kb_3835_510 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3835.lits.getD i 0)) 510 3 = true := by
  decide +kernel
theorem kg_3835_510 : IPChk.allR (Pts.glueIB K3835.lits KW_3835) 510 3 = true := by decide +kernel

end B334.E1x.Pts.S707
