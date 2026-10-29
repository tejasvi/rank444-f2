import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2693L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2693 of `S707`, parts 80 … 183, re-packed by predicted kernel memory (4.58 of 8.19 GB;
stage707_v5; the theorems are v3's `K2693C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2693_80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 80 24 = true := by
  decide +kernel
theorem kg_2693_80 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 80 24 = true := by decide +kernel
theorem kb_2693_104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 104 15 = true := by
  decide +kernel
theorem kg_2693_104 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 104 15 = true := by decide +kernel
theorem kb_2693_119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 119 7 = true := by
  decide +kernel
theorem kg_2693_119 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 119 7 = true := by decide +kernel
theorem kb_2693_126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 126 21 = true := by
  decide +kernel
theorem kg_2693_126 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 126 21 = true := by decide +kernel
theorem kb_2693_147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 147 11 = true := by
  decide +kernel
theorem kg_2693_147 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 147 11 = true := by decide +kernel
theorem kb_2693_158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2693.lits.getD i 0)) 158 26 = true := by
  decide +kernel
theorem kg_2693_158 : IPChk.allR (Pts.glueIB K2693.lits KW_2693) 158 26 = true := by decide +kernel

end B334.E1x.Pts.S707
