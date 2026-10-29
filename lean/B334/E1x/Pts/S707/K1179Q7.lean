import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1179L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1179 of `S707`, parts 790 … 853, re-packed by predicted kernel memory (3.52 of 8.19 GB;
stage707_v5; the theorems are v3's `K1179C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1179_790 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 790 1 = true := by
  decide +kernel
theorem kg_1179_790 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 790 1 = true := by decide +kernel
theorem kb_1179_791 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 791 7 = true := by
  decide +kernel
theorem kg_1179_791 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 791 7 = true := by decide +kernel
theorem kb_1179_798 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 798 14 = true := by
  decide +kernel
theorem kg_1179_798 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 798 14 = true := by decide +kernel
theorem kb_1179_812 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 812 20 = true := by
  decide +kernel
theorem kg_1179_812 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 812 20 = true := by decide +kernel
theorem kb_1179_832 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 832 20 = true := by
  decide +kernel
theorem kg_1179_832 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 832 20 = true := by decide +kernel
theorem kb_1179_852 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 852 2 = true := by
  decide +kernel
theorem kg_1179_852 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 852 2 = true := by decide +kernel

end B334.E1x.Pts.S707
