import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K981L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 981 of `S707`, parts 890 … 941, re-packed by predicted kernel memory (4.82 of 8.19 GB;
stage707_v5; the theorems are v3's `K981C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_981_890 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 890 17 = true := by
  decide +kernel
theorem kg_981_890 : IPChk.allR (Pts.glueIB K981.lits KW_981) 890 17 = true := by decide +kernel
theorem kb_981_907 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 907 23 = true := by
  decide +kernel
theorem kg_981_907 : IPChk.allR (Pts.glueIB K981.lits KW_981) 907 23 = true := by decide +kernel
theorem kb_981_930 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 930 2 = true := by
  decide +kernel
theorem kg_981_930 : IPChk.allR (Pts.glueIB K981.lits KW_981) 930 2 = true := by decide +kernel
theorem kb_981_932 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 932 3 = true := by
  decide +kernel
theorem kg_981_932 : IPChk.allR (Pts.glueIB K981.lits KW_981) 932 3 = true := by decide +kernel
theorem kb_981_935 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 935 2 = true := by
  decide +kernel
theorem kg_981_935 : IPChk.allR (Pts.glueIB K981.lits KW_981) 935 2 = true := by decide +kernel
theorem kb_981_937 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 937 5 = true := by
  decide +kernel
theorem kg_981_937 : IPChk.allR (Pts.glueIB K981.lits KW_981) 937 5 = true := by decide +kernel

end B334.E1x.Pts.S707
