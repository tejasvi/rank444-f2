import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J396
import B334.E1x.Pts.S707.J407
import B334.E1x.Pts.S707.J409
import B334.E1x.Pts.S707.J413
import B334.E1x.Pts.S707.J420
import B334.E1x.Pts.S707.J427
import B334.E1x.Pts.S707.J467
import B334.E1x.Pts.S707.J470
import B334.E1x.Pts.S707.J472
import B334.E1x.Pts.S707.K393L
import B334.E1x.Pts.S707.K394L
import B334.E1x.Pts.S707.K395L
import B334.E1x.Pts.S707.K406L
import B334.E1x.Pts.S707.K408L
import B334.E1x.Pts.S707.K412L
import B334.E1x.Pts.S707.K419L
import B334.E1x.Pts.S707.K426L
import B334.E1x.Pts.S707.K466L
import B334.E1x.Pts.S707.K469L
import B334.E1x.Pts.S707.K471L
import B334.E1x.Pts.S707.K393Q0
import B334.E1x.Pts.S707.K393Q1
import B334.E1x.Pts.S707.K393Q2
import B334.E1x.Pts.S707.K394C0
import B334.E1x.Pts.S707.K395Q0
import B334.E1x.Pts.S707.K395Q1
import B334.E1x.Pts.S707.K395Q2
import B334.E1x.Pts.S707.K406C0
import B334.E1x.Pts.S707.K408C0
import B334.E1x.Pts.S707.K412C0
import B334.E1x.Pts.S707.K419C0
import B334.E1x.Pts.S707.K426C0
import B334.E1x.Pts.S707.K466C0
import B334.E1x.Pts.S707.K469Q0
import B334.E1x.Pts.S707.K469Q1
import B334.E1x.Pts.S707.K469Q2
import B334.E1x.Pts.S707.K469Q3
import B334.E1x.Pts.S707.K469Q4
import B334.E1x.Pts.S707.K469Q5
import B334.E1x.Pts.S707.K469Q6
import B334.E1x.Pts.S707.K469Q7
import B334.E1x.Pts.S707.K469Q8
import B334.E1x.Pts.S707.K469Q9
import B334.E1x.Pts.S707.K471Q0
import B334.E1x.Pts.S707.K471Q1
import B334.E1x.Pts.S707.K471Q2
import B334.E1x.Pts.S707.K471Q3
import B334.E1x.Pts.S707.K471Q4
import B334.E1x.Pts.S707.K471Q5
import B334.E1x.Pts.S707.K471Q6
import B334.E1x.Pts.S707.K471Q7
import B334.E1x.Pts.S707.K471Q8
import B334.E1x.Pts.S707.K471Q9
import B334.E1x.Pts.S707.K469Q10
import B334.E1x.Pts.S707.K469Q11
import B334.E1x.Pts.S707.K469Q12
import B334.E1x.Pts.S707.K469Q13
import B334.E1x.Pts.S707.K469Q14
import B334.E1x.Pts.S707.K469Q15
import B334.E1x.Pts.S707.K469Q16
import B334.E1x.Pts.S707.K469Q17
import B334.E1x.Pts.S707.K469Q18
import B334.E1x.Pts.S707.K469Q19
import B334.E1x.Pts.S707.K469Q20
import B334.E1x.Pts.S707.K469Q21
import B334.E1x.Pts.S707.K469Q22
import B334.E1x.Pts.S707.K469Q23
import B334.E1x.Pts.S707.K469Q24
import B334.E1x.Pts.S707.K469Q25
import B334.E1x.Pts.S707.K469Q26
import B334.E1x.Pts.S707.K469Q27
import B334.E1x.Pts.S707.K469Q28
import B334.E1x.Pts.S707.K469Q29
import B334.E1x.Pts.S707.K469Q30
import B334.E1x.Pts.S707.K469Q31
import B334.E1x.Pts.S707.K471Q10
import B334.E1x.Pts.S707.K471Q11
import B334.E1x.Pts.S707.K471Q12
import B334.E1x.Pts.S707.K471Q13
import B334.E1x.Pts.S707.K471Q14
import B334.E1x.Pts.S707.K471Q15
import B334.E1x.Pts.S707.K471Q16

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 393 … 472 (stage707_v6): the v5 Fin's job blocks r88 … r108 as
theorems, joined into `grp6_4` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_88 : ∀ k, 393 ≤ k → k < 394 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 189 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 1 = true := kb_393_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 1 7 h0 kb_393_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 8 3 h1 kb_393_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 11 7 h2 kb_393_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 18 1 h3 kb_393_18
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 19 11 h4 kb_393_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 30 11 h5 kb_393_30
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 41 2 h6 kb_393_41
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 43 3 h7 kb_393_43
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 46 2 h8 kb_393_46
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 48 8 h9 kb_393_48
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 56 6 h10 kb_393_56
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 62 7 h11 kb_393_62
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 69 1 h12 kb_393_69
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 70 1 h13 kb_393_70
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 71 1 h14 kb_393_71
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 72 1 h15 kb_393_72
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 73 1 h16 kb_393_73
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 74 11 h17 kb_393_74
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 85 1 h18 kb_393_85
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 86 3 h19 kb_393_86
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 89 1 h20 kb_393_89
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 90 25 h21 kb_393_90
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 115 15 h22 kb_393_115
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 130 22 h23 kb_393_130
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 152 8 h24 kb_393_152
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 160 2 h25 kb_393_160
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 162 1 h26 kb_393_162
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 163 1 h27 kb_393_163
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K393.lits.getD i 0)) 0 164 25 h28 kb_393_164
    exact h29
  have hg : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 189 = true := by
    have h0 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 1 = true := kg_393_0
    have h1 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 8 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 1 7 h0 kg_393_1
    have h2 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 11 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 8 3 h1 kg_393_8
    have h3 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 18 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 11 7 h2 kg_393_11
    have h4 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 19 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 18 1 h3 kg_393_18
    have h5 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 30 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 19 11 h4 kg_393_19
    have h6 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 41 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 30 11 h5 kg_393_30
    have h7 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 43 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 41 2 h6 kg_393_41
    have h8 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 46 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 43 3 h7 kg_393_43
    have h9 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 48 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 46 2 h8 kg_393_46
    have h10 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 56 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 48 8 h9 kg_393_48
    have h11 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 62 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 56 6 h10 kg_393_56
    have h12 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 69 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 62 7 h11 kg_393_62
    have h13 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 70 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 69 1 h12 kg_393_69
    have h14 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 71 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 70 1 h13 kg_393_70
    have h15 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 72 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 71 1 h14 kg_393_71
    have h16 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 73 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 72 1 h15 kg_393_72
    have h17 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 74 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 73 1 h16 kg_393_73
    have h18 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 85 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 74 11 h17 kg_393_74
    have h19 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 86 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 85 1 h18 kg_393_85
    have h20 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 89 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 86 3 h19 kg_393_86
    have h21 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 90 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 89 1 h20 kg_393_89
    have h22 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 115 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 90 25 h21 kg_393_90
    have h23 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 130 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 115 15 h22 kg_393_115
    have h24 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 152 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 130 22 h23 kg_393_130
    have h25 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 160 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 152 8 h24 kg_393_152
    have h26 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 162 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 160 2 h25 kg_393_160
    have h27 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 163 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 162 1 h26 kg_393_162
    have h28 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 164 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 163 1 h27 kg_393_163
    have h29 : IPChk.allR (Pts.glueIB K393.lits KW_393) 0 189 = true := IPChk.allR_join (Pts.glueIB K393.lits KW_393) 0 164 25 h28 kg_393_164
    exact h29
  have hlen : K393.lits.length = 189 := by decide
  intro k h1 h2
  obtain rfl : k = 393 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 393) K393.lits KW_393
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_89 : ∀ k, 394 ≤ k → k < 395 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 29 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 8 = true := kb_394_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 8 3 h0 kb_394_8
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K394.lits.getD i 0)) 0 11 18 h1 kb_394_11
    exact h2
  have hg : IPChk.allR (Pts.glueIB K394.lits KW_394) 0 29 = true := by
    have h0 : IPChk.allR (Pts.glueIB K394.lits KW_394) 0 8 = true := kg_394_0
    have h1 : IPChk.allR (Pts.glueIB K394.lits KW_394) 0 11 = true := IPChk.allR_join (Pts.glueIB K394.lits KW_394) 0 8 3 h0 kg_394_8
    have h2 : IPChk.allR (Pts.glueIB K394.lits KW_394) 0 29 = true := IPChk.allR_join (Pts.glueIB K394.lits KW_394) 0 11 18 h1 kg_394_11
    exact h2
  have hlen : K394.lits.length = 29 := by decide
  intro k h1 h2
  obtain rfl : k = 394 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 394) K394.lits KW_394
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_90 : ∀ k, 395 ≤ k → k < 396 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 103 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 8 = true := kb_395_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 8 2 h0 kb_395_8
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 10 7 h1 kb_395_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 17 3 h2 kb_395_17
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 20 3 h3 kb_395_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 23 14 h4 kb_395_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 37 6 h5 kb_395_37
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 43 1 h6 kb_395_43
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 44 1 h7 kb_395_44
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 45 1 h8 kb_395_45
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 46 12 h9 kb_395_46
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 58 1 h10 kb_395_58
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 59 1 h11 kb_395_59
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 60 2 h12 kb_395_60
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 62 5 h13 kb_395_62
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 67 17 h14 kb_395_67
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 84 3 h15 kb_395_84
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 87 1 h16 kb_395_87
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 88 1 h17 kb_395_88
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 89 1 h18 kb_395_89
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 90 1 h19 kb_395_90
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 91 3 h20 kb_395_91
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 94 2 h21 kb_395_94
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 96 1 h22 kb_395_96
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 97 1 h23 kb_395_97
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 98 4 h24 kb_395_98
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 0 102 1 h25 kb_395_102
    exact h26
  have hg : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 103 = true := by
    have h0 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 8 = true := kg_395_0
    have h1 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 10 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 8 2 h0 kg_395_8
    have h2 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 17 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 10 7 h1 kg_395_10
    have h3 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 20 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 17 3 h2 kg_395_17
    have h4 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 23 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 20 3 h3 kg_395_20
    have h5 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 37 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 23 14 h4 kg_395_23
    have h6 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 43 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 37 6 h5 kg_395_37
    have h7 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 44 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 43 1 h6 kg_395_43
    have h8 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 45 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 44 1 h7 kg_395_44
    have h9 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 46 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 45 1 h8 kg_395_45
    have h10 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 58 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 46 12 h9 kg_395_46
    have h11 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 59 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 58 1 h10 kg_395_58
    have h12 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 60 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 59 1 h11 kg_395_59
    have h13 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 62 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 60 2 h12 kg_395_60
    have h14 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 67 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 62 5 h13 kg_395_62
    have h15 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 84 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 67 17 h14 kg_395_67
    have h16 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 87 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 84 3 h15 kg_395_84
    have h17 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 88 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 87 1 h16 kg_395_87
    have h18 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 89 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 88 1 h17 kg_395_88
    have h19 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 90 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 89 1 h18 kg_395_89
    have h20 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 91 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 90 1 h19 kg_395_90
    have h21 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 94 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 91 3 h20 kg_395_91
    have h22 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 96 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 94 2 h21 kg_395_94
    have h23 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 97 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 96 1 h22 kg_395_96
    have h24 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 98 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 97 1 h23 kg_395_97
    have h25 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 102 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 98 4 h24 kg_395_98
    have h26 : IPChk.allR (Pts.glueIB K395.lits KW_395) 0 103 = true := IPChk.allR_join (Pts.glueIB K395.lits KW_395) 0 102 1 h25 kg_395_102
    exact h26
  have hlen : K395.lits.length = 103 := by decide
  intro k h1 h2
  obtain rfl : k = 395 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 395) K395.lits KW_395
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_91 : ∀ k, 396 ≤ k → k < 406 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_396 JW_396 396 10 jr_396
theorem jr6_92 : ∀ k, 406 ≤ k → k < 407 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 62 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 2 = true := kb_406_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 2 4 h0 kb_406_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 6 1 h1 kb_406_6
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 7 14 h2 kb_406_7
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 21 11 h3 kb_406_21
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 32 27 h4 kb_406_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K406.lits.getD i 0)) 0 59 3 h5 kb_406_59
    exact h6
  have hg : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 62 = true := by
    have h0 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 2 = true := kg_406_0
    have h1 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 6 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 2 4 h0 kg_406_2
    have h2 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 7 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 6 1 h1 kg_406_6
    have h3 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 21 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 7 14 h2 kg_406_7
    have h4 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 32 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 21 11 h3 kg_406_21
    have h5 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 59 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 32 27 h4 kg_406_32
    have h6 : IPChk.allR (Pts.glueIB K406.lits KW_406) 0 62 = true := IPChk.allR_join (Pts.glueIB K406.lits KW_406) 0 59 3 h5 kg_406_59
    exact h6
  have hlen : K406.lits.length = 62 := by decide
  intro k h1 h2
  obtain rfl : k = 406 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 406) K406.lits KW_406
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_93 : ∀ k, 407 ≤ k → k < 408 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_407 JW_407 407 1 jr_407
theorem jr6_94 : ∀ k, 408 ≤ k → k < 409 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 60 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 1 = true := kb_408_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 1 1 h0 kb_408_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 2 3 h1 kb_408_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 5 1 h2 kb_408_5
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 6 9 h3 kb_408_6
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 15 8 h4 kb_408_15
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 23 2 h5 kb_408_23
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 25 4 h6 kb_408_25
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 29 24 h7 kb_408_29
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 53 1 h8 kb_408_53
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 54 1 h9 kb_408_54
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 55 4 h10 kb_408_55
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K408.lits.getD i 0)) 0 59 1 h11 kb_408_59
    exact h12
  have hg : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 60 = true := by
    have h0 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 1 = true := kg_408_0
    have h1 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 2 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 1 1 h0 kg_408_1
    have h2 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 5 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 2 3 h1 kg_408_2
    have h3 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 6 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 5 1 h2 kg_408_5
    have h4 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 15 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 6 9 h3 kg_408_6
    have h5 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 23 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 15 8 h4 kg_408_15
    have h6 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 25 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 23 2 h5 kg_408_23
    have h7 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 29 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 25 4 h6 kg_408_25
    have h8 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 53 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 29 24 h7 kg_408_29
    have h9 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 54 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 53 1 h8 kg_408_53
    have h10 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 55 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 54 1 h9 kg_408_54
    have h11 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 59 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 55 4 h10 kg_408_55
    have h12 : IPChk.allR (Pts.glueIB K408.lits KW_408) 0 60 = true := IPChk.allR_join (Pts.glueIB K408.lits KW_408) 0 59 1 h11 kg_408_59
    exact h12
  have hlen : K408.lits.length = 60 := by decide
  intro k h1 h2
  obtain rfl : k = 408 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 408) K408.lits KW_408
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_95 : ∀ k, 409 ≤ k → k < 412 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_409 JW_409 409 3 jr_409
theorem jr6_96 : ∀ k, 412 ≤ k → k < 413 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 46 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 4 = true := kb_412_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 4 1 h0 kb_412_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 5 1 h1 kb_412_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 6 11 h2 kb_412_6
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 17 4 h3 kb_412_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 21 5 h4 kb_412_21
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 26 12 h5 kb_412_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 38 1 h6 kb_412_38
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 39 1 h7 kb_412_39
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 40 5 h8 kb_412_40
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K412.lits.getD i 0)) 0 45 1 h9 kb_412_45
    exact h10
  have hg : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 46 = true := by
    have h0 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 4 = true := kg_412_0
    have h1 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 5 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 4 1 h0 kg_412_4
    have h2 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 6 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 5 1 h1 kg_412_5
    have h3 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 17 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 6 11 h2 kg_412_6
    have h4 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 21 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 17 4 h3 kg_412_17
    have h5 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 26 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 21 5 h4 kg_412_21
    have h6 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 38 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 26 12 h5 kg_412_26
    have h7 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 39 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 38 1 h6 kg_412_38
    have h8 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 40 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 39 1 h7 kg_412_39
    have h9 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 45 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 40 5 h8 kg_412_40
    have h10 : IPChk.allR (Pts.glueIB K412.lits KW_412) 0 46 = true := IPChk.allR_join (Pts.glueIB K412.lits KW_412) 0 45 1 h9 kg_412_45
    exact h10
  have hlen : K412.lits.length = 46 := by decide
  intro k h1 h2
  obtain rfl : k = 412 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 412) K412.lits KW_412
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_97 : ∀ k, 413 ≤ k → k < 419 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_413 JW_413 413 6 jr_413
theorem jr6_98 : ∀ k, 419 ≤ k → k < 420 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 69 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 1 = true := kb_419_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 1 6 h0 kb_419_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 7 1 h1 kb_419_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 8 20 h2 kb_419_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 28 6 h3 kb_419_28
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 34 3 h4 kb_419_34
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 37 7 h5 kb_419_37
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 44 23 h6 kb_419_44
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K419.lits.getD i 0)) 0 67 2 h7 kb_419_67
    exact h8
  have hg : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 69 = true := by
    have h0 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 1 = true := kg_419_0
    have h1 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 7 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 1 6 h0 kg_419_1
    have h2 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 8 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 7 1 h1 kg_419_7
    have h3 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 28 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 8 20 h2 kg_419_8
    have h4 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 34 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 28 6 h3 kg_419_28
    have h5 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 37 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 34 3 h4 kg_419_34
    have h6 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 44 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 37 7 h5 kg_419_37
    have h7 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 67 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 44 23 h6 kg_419_44
    have h8 : IPChk.allR (Pts.glueIB K419.lits KW_419) 0 69 = true := IPChk.allR_join (Pts.glueIB K419.lits KW_419) 0 67 2 h7 kg_419_67
    exact h8
  have hlen : K419.lits.length = 69 := by decide
  intro k h1 h2
  obtain rfl : k = 419 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 419) K419.lits KW_419
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_99 : ∀ k, 420 ≤ k → k < 425 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_420 JW_420 420 5 jr_420
theorem jr6_100 : ∀ k, 425 ≤ k → k < 426 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_420 JW_420 425 1 jr_425
theorem jr6_101 : ∀ k, 426 ≤ k → k < 427 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 38 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 1 = true := kb_426_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 1 1 h0 kb_426_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 2 13 h1 kb_426_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 15 9 h2 kb_426_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K426.lits.getD i 0)) 0 24 14 h3 kb_426_24
    exact h4
  have hg : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 38 = true := by
    have h0 : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 1 = true := kg_426_0
    have h1 : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 2 = true := IPChk.allR_join (Pts.glueIB K426.lits KW_426) 0 1 1 h0 kg_426_1
    have h2 : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 15 = true := IPChk.allR_join (Pts.glueIB K426.lits KW_426) 0 2 13 h1 kg_426_2
    have h3 : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 24 = true := IPChk.allR_join (Pts.glueIB K426.lits KW_426) 0 15 9 h2 kg_426_15
    have h4 : IPChk.allR (Pts.glueIB K426.lits KW_426) 0 38 = true := IPChk.allR_join (Pts.glueIB K426.lits KW_426) 0 24 14 h3 kg_426_24
    exact h4
  have hlen : K426.lits.length = 38 := by decide
  intro k h1 h2
  obtain rfl : k = 426 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 426) K426.lits KW_426
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_102 : ∀ k, 427 ≤ k → k < 466 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_427 JW_427 427 39 jr_427
theorem jr6_103 : ∀ k, 466 ≤ k → k < 467 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 8 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 2 = true := kb_466_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 2 2 h0 kb_466_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 4 3 h1 kb_466_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K466.lits.getD i 0)) 0 7 1 h2 kb_466_7
    exact h3
  have hg : IPChk.allR (Pts.glueIB K466.lits KW_466) 0 8 = true := by
    have h0 : IPChk.allR (Pts.glueIB K466.lits KW_466) 0 2 = true := kg_466_0
    have h1 : IPChk.allR (Pts.glueIB K466.lits KW_466) 0 4 = true := IPChk.allR_join (Pts.glueIB K466.lits KW_466) 0 2 2 h0 kg_466_2
    have h2 : IPChk.allR (Pts.glueIB K466.lits KW_466) 0 7 = true := IPChk.allR_join (Pts.glueIB K466.lits KW_466) 0 4 3 h1 kg_466_4
    have h3 : IPChk.allR (Pts.glueIB K466.lits KW_466) 0 8 = true := IPChk.allR_join (Pts.glueIB K466.lits KW_466) 0 7 1 h2 kg_466_7
    exact h3
  have hlen : K466.lits.length = 8 := by decide
  intro k h1 h2
  obtain rfl : k = 466 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 466) K466.lits KW_466
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_104 : ∀ k, 467 ≤ k → k < 469 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_467 JW_467 467 2 jr_467
theorem jr6_105 : ∀ k, 469 ≤ k → k < 470 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5037 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2 = true := kb_469_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2 2 h0 kb_469_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4 8 h1 kb_469_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 12 3 h2 kb_469_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 15 8 h3 kb_469_15
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 23 8 h4 kb_469_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 31 5 h5 kb_469_31
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 36 6 h6 kb_469_36
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 42 9 h7 kb_469_42
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 51 6 h8 kb_469_51
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 57 3 h9 kb_469_57
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 60 15 h10 kb_469_60
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 75 5 h11 kb_469_75
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 80 8 h12 kb_469_80
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 88 8 h13 kb_469_88
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 96 3 h14 kb_469_96
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 99 8 h15 kb_469_99
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 107 8 h16 kb_469_107
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 115 2 h17 kb_469_115
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 117 8 h18 kb_469_117
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 125 9 h19 kb_469_125
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 134 3 h20 kb_469_134
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 137 12 h21 kb_469_137
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 149 2 h22 kb_469_149
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 151 1 h23 kb_469_151
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 152 1 h24 kb_469_152
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 153 18 h25 kb_469_153
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 171 13 h26 kb_469_171
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 184 6 h27 kb_469_184
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 190 2 h28 kb_469_190
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 192 13 h29 kb_469_192
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 205 9 h30 kb_469_205
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 214 3 h31 kb_469_214
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 217 8 h32 kb_469_217
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 225 20 h33 kb_469_225
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 245 1 h34 kb_469_245
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 246 3 h35 kb_469_246
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 249 5 h36 kb_469_249
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 254 8 h37 kb_469_254
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 262 2 h38 kb_469_262
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 264 21 h39 kb_469_264
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 285 9 h40 kb_469_285
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 294 19 h41 kb_469_294
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 313 6 h42 kb_469_313
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 319 20 h43 kb_469_319
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 339 35 h44 kb_469_339
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 461 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 374 87 h45 kb_469_374
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 461 7 h46 kb_469_461
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 468 8 h47 kb_469_468
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 476 8 h48 kb_469_476
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 484 7 h49 kb_469_484
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 491 2 h50 kb_469_491
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 493 29 h51 kb_469_493
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 522 2 h52 kb_469_522
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 524 6 h53 kb_469_524
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 530 2 h54 kb_469_530
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 532 21 h55 kb_469_532
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 553 25 h56 kb_469_553
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 578 10 h57 kb_469_578
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 588 13 h58 kb_469_588
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 605 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 601 4 h59 kb_469_601
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 615 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 605 10 h60 kb_469_605
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 617 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 615 2 h61 kb_469_615
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 617 29 h62 kb_469_617
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 646 2 h63 kb_469_646
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 648 6 h64 kb_469_648
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 654 2 h65 kb_469_654
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 656 14 h66 kb_469_656
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 670 8 h67 kb_469_670
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 678 8 h68 kb_469_678
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 704 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 686 18 h69 kb_469_686
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 705 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 704 1 h70 kb_469_704
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 708 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 705 3 h71 kb_469_705
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 711 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 708 3 h72 kb_469_708
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 711 15 h73 kb_469_711
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 768 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 726 42 h74 kb_469_726
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 768 29 h75 kb_469_768
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 799 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 797 2 h76 kb_469_797
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 799 29 h77 kb_469_799
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 828 2 h78 kb_469_828
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 836 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 830 6 h79 kb_469_830
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 838 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 836 2 h80 kb_469_836
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 860 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 838 22 h81 kb_469_838
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 864 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 860 4 h82 kb_469_860
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 893 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 864 29 h83 kb_469_864
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 893 21 h84 kb_469_893
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 923 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 914 9 h85 kb_469_914
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 923 1 h86 kb_469_923
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 925 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 924 1 h87 kb_469_924
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 937 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 925 12 h88 kb_469_925
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 964 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 937 27 h89 kb_469_937
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 966 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 964 2 h90 kb_469_964
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 966 25 h91 kb_469_966
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 991 5 h92 kb_469_991
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1010 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 996 14 h93 kb_469_996
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1012 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1010 2 h94 kb_469_1010
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1018 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1012 6 h95 kb_469_1012
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1020 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1018 2 h96 kb_469_1018
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1038 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1020 18 h97 kb_469_1020
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1047 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1038 9 h98 kb_469_1038
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1049 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1047 2 h99 kb_469_1047
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1049 20 h100 kb_469_1049
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1069 2 h101 kb_469_1069
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1071 29 h102 kb_469_1071
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1100 8 h103 kb_469_1100
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1108 19 h104 kb_469_1108
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1127 6 h105 kb_469_1127
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1133 1 h106 kb_469_1133
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1134 9 h107 kb_469_1134
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1143 7 h108 kb_469_1143
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1150 23 h109 kb_469_1150
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1173 2 h110 kb_469_1173
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1175 6 h111 kb_469_1175
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1181 2 h112 kb_469_1181
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1183 21 h113 kb_469_1183
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1204 39 h114 kb_469_1204
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1243 8 h115 kb_469_1243
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1251 16 h116 kb_469_1251
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1267 2 h117 kb_469_1267
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1269 5 h118 kb_469_1269
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1274 15 h119 kb_469_1274
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1289 29 h120 kb_469_1289
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1318 2 h121 kb_469_1318
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1320 12 h122 kb_469_1320
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1332 2 h123 kb_469_1332
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1334 4 h124 kb_469_1334
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1338 2 h125 kb_469_1338
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1340 39 h126 kb_469_1340
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1440 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1379 61 h127 kb_469_1379
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1440 14 h128 kb_469_1440
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1454 10 h129 kb_469_1454
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1464 22 h130 kb_469_1464
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1486 6 h131 kb_469_1486
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1492 37 h132 kb_469_1492
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1529 27 h133 kb_469_1529
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1556 20 h134 kb_469_1556
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1576 2 h135 kb_469_1576
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1578 32 h136 kb_469_1578
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1610 8 h137 kb_469_1610
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1625 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1618 7 h138 kb_469_1618
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1625 13 h139 kb_469_1625
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1638 23 h140 kb_469_1638
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1661 19 h141 kb_469_1661
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1680 15 h142 kb_469_1680
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1695 6 h143 kb_469_1695
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1703 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1701 2 h144 kb_469_1701
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1727 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1703 24 h145 kb_469_1703
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1729 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1727 2 h146 kb_469_1727
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1748 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1729 19 h147 kb_469_1729
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1777 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1748 29 h148 kb_469_1748
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1777 16 h149 kb_469_1777
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1793 1 h150 kb_469_1793
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1799 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1794 5 h151 kb_469_1794
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1799 31 h152 kb_469_1799
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1850 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1830 20 h153 kb_469_1830
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1858 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1850 8 h154 kb_469_1850
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1858 19 h155 kb_469_1858
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1877 1 h156 kb_469_1877
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1897 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1878 19 h157 kb_469_1878
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1982 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1897 85 h158 kb_469_1897
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1982 9 h159 kb_469_1982
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2002 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 1991 11 h160 kb_469_1991
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2026 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2002 24 h161 kb_469_2002
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2026 2 h162 kb_469_2026
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2040 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2028 12 h163 kb_469_2028
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2055 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2040 15 h164 kb_469_2040
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2057 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2055 2 h165 kb_469_2055
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2057 15 h166 kb_469_2057
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2079 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2072 7 h167 kb_469_2072
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2079 23 h168 kb_469_2079
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2102 2 h169 kb_469_2102
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2104 17 h170 kb_469_2104
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2121 27 h171 kb_469_2121
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2148 20 h172 kb_469_2148
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2168 14 h173 kb_469_2168
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2182 55 h174 kb_469_2182
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2237 30 h175 kb_469_2237
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2267 5 h176 kb_469_2267
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2272 27 h177 kb_469_2272
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2299 2 h178 kb_469_2299
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2301 12 h179 kb_469_2301
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2313 15 h180 kb_469_2313
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2328 2 h181 kb_469_2328
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2330 12 h182 kb_469_2330
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2342 3 h183 kb_469_2342
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2345 6 h184 kb_469_2345
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2351 3 h185 kb_469_2351
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2354 14 h186 kb_469_2354
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2368 10 h187 kb_469_2368
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2378 3 h188 kb_469_2378
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2381 24 h189 kb_469_2381
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2405 46 h190 kb_469_2405
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2451 9 h191 kb_469_2451
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2460 29 h192 kb_469_2460
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2489 16 h193 kb_469_2489
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2505 2 h194 kb_469_2505
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2507 16 h195 kb_469_2507
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2523 4 h196 kb_469_2523
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2527 23 h197 kb_469_2527
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2550 7 h198 kb_469_2550
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2557 19 h199 kb_469_2557
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2576 25 h200 kb_469_2576
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2601 28 h201 kb_469_2601
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2629 17 h202 kb_469_2629
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2702 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2646 56 h203 kb_469_2646
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2702 56 h204 kb_469_2702
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2779 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2758 21 h205 kb_469_2758
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2779 2 h206 kb_469_2779
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2781 12 h207 kb_469_2781
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2793 3 h208 kb_469_2793
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2796 6 h209 kb_469_2796
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2802 2 h210 kb_469_2802
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2804 19 h211 kb_469_2804
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2825 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2823 2 h212 kb_469_2823
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2840 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2825 15 h213 kb_469_2825
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2865 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2840 25 h214 kb_469_2840
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2876 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2865 11 h215 kb_469_2865
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2896 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2876 20 h216 kb_469_2876
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2985 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2896 89 h217 kb_469_2896
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3021 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 2985 36 h218 kb_469_2985
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3021 1 h219 kb_469_3021
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3031 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3022 9 h220 kb_469_3022
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3060 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3031 29 h221 kb_469_3031
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3060 62 h222 kb_469_3060
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3122 17 h223 kb_469_3122
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3139 15 h224 kb_469_3139
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3154 5 h225 kb_469_3154
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3159 23 h226 kb_469_3159
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3182 15 h227 kb_469_3182
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3197 18 h228 kb_469_3197
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3215 52 h229 kb_469_3215
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3267 1 h230 kb_469_3267
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3268 30 h231 kb_469_3268
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3298 1 h232 kb_469_3298
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3299 16 h233 kb_469_3299
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3315 49 h234 kb_469_3315
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3364 6 h235 kb_469_3364
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3370 14 h236 kb_469_3370
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3384 30 h237 kb_469_3384
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3414 17 h238 kb_469_3414
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3431 21 h239 kb_469_3431
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3452 29 h240 kb_469_3452
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3481 7 h241 kb_469_3481
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3488 29 h242 kb_469_3488
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3517 10 h243 kb_469_3517
    have h245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3527 84 h244 kb_469_3527
    have h246 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3611 13 h245 kb_469_3611
    have h247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3645 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3624 21 h246 kb_469_3624
    have h248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3645 19 h247 kb_469_3645
    have h249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3664 13 h248 kb_469_3664
    have h250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3677 1 h249 kb_469_3677
    have h251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3708 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3678 30 h250 kb_469_3678
    have h252 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3709 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3708 1 h251 kb_469_3708
    have h253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3709 15 h252 kb_469_3709
    have h254 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3752 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3724 28 h253 kb_469_3724
    have h255 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3752 9 h254 kb_469_3752
    have h256 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3790 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3761 29 h255 kb_469_3761
    have h257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3790 6 h256 kb_469_3790
    have h258 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3796 15 h257 kb_469_3796
    have h259 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3838 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3811 27 h258 kb_469_3811
    have h260 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3864 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3838 26 h259 kb_469_3838
    have h261 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3892 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3864 28 h260 kb_469_3864
    have h262 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3892 43 h261 kb_469_3892
    have h263 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3981 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3935 46 h262 kb_469_3935
    have h264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4038 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 3981 57 h263 kb_469_3981
    have h265 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4038 5 h264 kb_469_4038
    have h266 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4063 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4043 20 h265 kb_469_4043
    have h267 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4063 6 h266 kb_469_4063
    have h268 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4069 13 h267 kb_469_4069
    have h269 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4082 23 h268 kb_469_4082
    have h270 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4105 28 h269 kb_469_4105
    have h271 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4133 21 h270 kb_469_4133
    have h272 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4154 32 h271 kb_469_4154
    have h273 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4186 27 h272 kb_469_4186
    have h274 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4213 1 h273 kb_469_4213
    have h275 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4214 6 h274 kb_469_4214
    have h276 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4220 6 h275 kb_469_4220
    have h277 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4226 17 h276 kb_469_4226
    have h278 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4243 11 h277 kb_469_4243
    have h279 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4254 1 h278 kb_469_4254
    have h280 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4255 7 h279 kb_469_4255
    have h281 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4262 12 h280 kb_469_4262
    have h282 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4274 17 h281 kb_469_4274
    have h283 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4295 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4291 4 h282 kb_469_4291
    have h284 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4295 6 h283 kb_469_4295
    have h285 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4301 19 h284 kb_469_4301
    have h286 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4320 56 h285 kb_469_4320
    have h287 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4376 60 h286 kb_469_4376
    have h288 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4436 6 h287 kb_469_4436
    have h289 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4442 22 h288 kb_469_4442
    have h290 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4464 69 h289 kb_469_4464
    have h291 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4533 51 h290 kb_469_4533
    have h292 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4584 23 h291 kb_469_4584
    have h293 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4607 31 h292 kb_469_4607
    have h294 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4638 5 h293 kb_469_4638
    have h295 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4643 1 h294 kb_469_4643
    have h296 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4651 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4644 7 h295 kb_469_4644
    have h297 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4651 1 h296 kb_469_4651
    have h298 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4652 10 h297 kb_469_4652
    have h299 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4662 6 h298 kb_469_4662
    have h300 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4668 17 h299 kb_469_4668
    have h301 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4685 56 h300 kb_469_4685
    have h302 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4819 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4741 78 h301 kb_469_4741
    have h303 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4838 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4819 19 h302 kb_469_4819
    have h304 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4838 3 h303 kb_469_4838
    have h305 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4863 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4841 22 h304 kb_469_4841
    have h306 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4885 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4863 22 h305 kb_469_4863
    have h307 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4912 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4885 27 h306 kb_469_4885
    have h308 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4912 31 h307 kb_469_4912
    have h309 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4943 11 h308 kb_469_4943
    have h310 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4954 1 h309 kb_469_4954
    have h311 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4964 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4955 9 h310 kb_469_4955
    have h312 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4976 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4964 12 h311 kb_469_4964
    have h313 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4976 15 h312 kb_469_4976
    have h314 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5003 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 4991 12 h313 kb_469_4991
    have h315 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5009 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5003 6 h314 kb_469_5003
    have h316 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5035 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5009 26 h315 kb_469_5009
    have h317 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5037 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K469.lits.getD i 0)) 0 5035 2 h316 kb_469_5035
    exact h317
  have hg : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 5037 = true := by
    have h0 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2 = true := kg_469_0
    have h1 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2 2 h0 kg_469_2
    have h2 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 12 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4 8 h1 kg_469_4
    have h3 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 15 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 12 3 h2 kg_469_12
    have h4 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 23 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 15 8 h3 kg_469_15
    have h5 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 31 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 23 8 h4 kg_469_23
    have h6 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 36 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 31 5 h5 kg_469_31
    have h7 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 42 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 36 6 h6 kg_469_36
    have h8 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 51 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 42 9 h7 kg_469_42
    have h9 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 57 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 51 6 h8 kg_469_51
    have h10 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 60 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 57 3 h9 kg_469_57
    have h11 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 75 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 60 15 h10 kg_469_60
    have h12 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 80 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 75 5 h11 kg_469_75
    have h13 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 88 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 80 8 h12 kg_469_80
    have h14 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 96 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 88 8 h13 kg_469_88
    have h15 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 99 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 96 3 h14 kg_469_96
    have h16 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 107 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 99 8 h15 kg_469_99
    have h17 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 115 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 107 8 h16 kg_469_107
    have h18 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 117 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 115 2 h17 kg_469_115
    have h19 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 125 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 117 8 h18 kg_469_117
    have h20 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 134 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 125 9 h19 kg_469_125
    have h21 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 137 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 134 3 h20 kg_469_134
    have h22 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 149 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 137 12 h21 kg_469_137
    have h23 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 151 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 149 2 h22 kg_469_149
    have h24 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 152 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 151 1 h23 kg_469_151
    have h25 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 153 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 152 1 h24 kg_469_152
    have h26 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 171 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 153 18 h25 kg_469_153
    have h27 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 184 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 171 13 h26 kg_469_171
    have h28 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 190 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 184 6 h27 kg_469_184
    have h29 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 192 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 190 2 h28 kg_469_190
    have h30 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 205 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 192 13 h29 kg_469_192
    have h31 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 214 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 205 9 h30 kg_469_205
    have h32 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 217 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 214 3 h31 kg_469_214
    have h33 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 225 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 217 8 h32 kg_469_217
    have h34 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 245 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 225 20 h33 kg_469_225
    have h35 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 246 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 245 1 h34 kg_469_245
    have h36 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 249 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 246 3 h35 kg_469_246
    have h37 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 254 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 249 5 h36 kg_469_249
    have h38 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 262 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 254 8 h37 kg_469_254
    have h39 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 264 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 262 2 h38 kg_469_262
    have h40 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 285 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 264 21 h39 kg_469_264
    have h41 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 294 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 285 9 h40 kg_469_285
    have h42 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 313 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 294 19 h41 kg_469_294
    have h43 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 319 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 313 6 h42 kg_469_313
    have h44 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 339 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 319 20 h43 kg_469_319
    have h45 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 374 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 339 35 h44 kg_469_339
    have h46 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 461 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 374 87 h45 kg_469_374
    have h47 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 468 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 461 7 h46 kg_469_461
    have h48 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 476 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 468 8 h47 kg_469_468
    have h49 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 484 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 476 8 h48 kg_469_476
    have h50 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 491 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 484 7 h49 kg_469_484
    have h51 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 493 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 491 2 h50 kg_469_491
    have h52 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 522 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 493 29 h51 kg_469_493
    have h53 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 524 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 522 2 h52 kg_469_522
    have h54 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 530 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 524 6 h53 kg_469_524
    have h55 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 532 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 530 2 h54 kg_469_530
    have h56 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 553 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 532 21 h55 kg_469_532
    have h57 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 578 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 553 25 h56 kg_469_553
    have h58 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 588 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 578 10 h57 kg_469_578
    have h59 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 601 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 588 13 h58 kg_469_588
    have h60 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 605 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 601 4 h59 kg_469_601
    have h61 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 615 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 605 10 h60 kg_469_605
    have h62 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 617 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 615 2 h61 kg_469_615
    have h63 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 646 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 617 29 h62 kg_469_617
    have h64 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 648 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 646 2 h63 kg_469_646
    have h65 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 654 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 648 6 h64 kg_469_648
    have h66 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 656 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 654 2 h65 kg_469_654
    have h67 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 670 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 656 14 h66 kg_469_656
    have h68 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 678 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 670 8 h67 kg_469_670
    have h69 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 686 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 678 8 h68 kg_469_678
    have h70 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 704 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 686 18 h69 kg_469_686
    have h71 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 705 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 704 1 h70 kg_469_704
    have h72 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 708 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 705 3 h71 kg_469_705
    have h73 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 711 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 708 3 h72 kg_469_708
    have h74 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 726 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 711 15 h73 kg_469_711
    have h75 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 768 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 726 42 h74 kg_469_726
    have h76 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 797 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 768 29 h75 kg_469_768
    have h77 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 799 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 797 2 h76 kg_469_797
    have h78 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 828 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 799 29 h77 kg_469_799
    have h79 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 830 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 828 2 h78 kg_469_828
    have h80 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 836 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 830 6 h79 kg_469_830
    have h81 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 838 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 836 2 h80 kg_469_836
    have h82 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 860 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 838 22 h81 kg_469_838
    have h83 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 864 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 860 4 h82 kg_469_860
    have h84 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 893 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 864 29 h83 kg_469_864
    have h85 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 914 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 893 21 h84 kg_469_893
    have h86 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 923 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 914 9 h85 kg_469_914
    have h87 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 924 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 923 1 h86 kg_469_923
    have h88 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 925 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 924 1 h87 kg_469_924
    have h89 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 937 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 925 12 h88 kg_469_925
    have h90 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 964 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 937 27 h89 kg_469_937
    have h91 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 966 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 964 2 h90 kg_469_964
    have h92 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 991 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 966 25 h91 kg_469_966
    have h93 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 996 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 991 5 h92 kg_469_991
    have h94 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1010 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 996 14 h93 kg_469_996
    have h95 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1012 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1010 2 h94 kg_469_1010
    have h96 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1018 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1012 6 h95 kg_469_1012
    have h97 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1020 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1018 2 h96 kg_469_1018
    have h98 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1038 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1020 18 h97 kg_469_1020
    have h99 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1047 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1038 9 h98 kg_469_1038
    have h100 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1049 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1047 2 h99 kg_469_1047
    have h101 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1069 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1049 20 h100 kg_469_1049
    have h102 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1071 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1069 2 h101 kg_469_1069
    have h103 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1100 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1071 29 h102 kg_469_1071
    have h104 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1108 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1100 8 h103 kg_469_1100
    have h105 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1127 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1108 19 h104 kg_469_1108
    have h106 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1133 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1127 6 h105 kg_469_1127
    have h107 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1134 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1133 1 h106 kg_469_1133
    have h108 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1143 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1134 9 h107 kg_469_1134
    have h109 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1150 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1143 7 h108 kg_469_1143
    have h110 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1173 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1150 23 h109 kg_469_1150
    have h111 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1175 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1173 2 h110 kg_469_1173
    have h112 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1181 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1175 6 h111 kg_469_1175
    have h113 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1183 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1181 2 h112 kg_469_1181
    have h114 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1204 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1183 21 h113 kg_469_1183
    have h115 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1243 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1204 39 h114 kg_469_1204
    have h116 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1251 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1243 8 h115 kg_469_1243
    have h117 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1267 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1251 16 h116 kg_469_1251
    have h118 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1269 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1267 2 h117 kg_469_1267
    have h119 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1274 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1269 5 h118 kg_469_1269
    have h120 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1289 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1274 15 h119 kg_469_1274
    have h121 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1318 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1289 29 h120 kg_469_1289
    have h122 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1320 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1318 2 h121 kg_469_1318
    have h123 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1332 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1320 12 h122 kg_469_1320
    have h124 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1334 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1332 2 h123 kg_469_1332
    have h125 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1338 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1334 4 h124 kg_469_1334
    have h126 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1340 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1338 2 h125 kg_469_1338
    have h127 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1379 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1340 39 h126 kg_469_1340
    have h128 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1440 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1379 61 h127 kg_469_1379
    have h129 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1454 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1440 14 h128 kg_469_1440
    have h130 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1464 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1454 10 h129 kg_469_1454
    have h131 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1486 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1464 22 h130 kg_469_1464
    have h132 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1492 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1486 6 h131 kg_469_1486
    have h133 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1529 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1492 37 h132 kg_469_1492
    have h134 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1556 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1529 27 h133 kg_469_1529
    have h135 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1576 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1556 20 h134 kg_469_1556
    have h136 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1578 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1576 2 h135 kg_469_1576
    have h137 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1610 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1578 32 h136 kg_469_1578
    have h138 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1618 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1610 8 h137 kg_469_1610
    have h139 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1625 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1618 7 h138 kg_469_1618
    have h140 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1638 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1625 13 h139 kg_469_1625
    have h141 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1661 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1638 23 h140 kg_469_1638
    have h142 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1680 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1661 19 h141 kg_469_1661
    have h143 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1695 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1680 15 h142 kg_469_1680
    have h144 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1701 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1695 6 h143 kg_469_1695
    have h145 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1703 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1701 2 h144 kg_469_1701
    have h146 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1727 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1703 24 h145 kg_469_1703
    have h147 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1729 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1727 2 h146 kg_469_1727
    have h148 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1748 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1729 19 h147 kg_469_1729
    have h149 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1777 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1748 29 h148 kg_469_1748
    have h150 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1793 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1777 16 h149 kg_469_1777
    have h151 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1794 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1793 1 h150 kg_469_1793
    have h152 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1799 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1794 5 h151 kg_469_1794
    have h153 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1830 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1799 31 h152 kg_469_1799
    have h154 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1850 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1830 20 h153 kg_469_1830
    have h155 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1858 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1850 8 h154 kg_469_1850
    have h156 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1877 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1858 19 h155 kg_469_1858
    have h157 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1878 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1877 1 h156 kg_469_1877
    have h158 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1897 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1878 19 h157 kg_469_1878
    have h159 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1982 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1897 85 h158 kg_469_1897
    have h160 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 1991 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1982 9 h159 kg_469_1982
    have h161 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2002 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 1991 11 h160 kg_469_1991
    have h162 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2026 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2002 24 h161 kg_469_2002
    have h163 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2028 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2026 2 h162 kg_469_2026
    have h164 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2040 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2028 12 h163 kg_469_2028
    have h165 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2055 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2040 15 h164 kg_469_2040
    have h166 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2057 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2055 2 h165 kg_469_2055
    have h167 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2072 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2057 15 h166 kg_469_2057
    have h168 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2079 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2072 7 h167 kg_469_2072
    have h169 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2102 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2079 23 h168 kg_469_2079
    have h170 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2104 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2102 2 h169 kg_469_2102
    have h171 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2121 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2104 17 h170 kg_469_2104
    have h172 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2148 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2121 27 h171 kg_469_2121
    have h173 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2168 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2148 20 h172 kg_469_2148
    have h174 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2182 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2168 14 h173 kg_469_2168
    have h175 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2237 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2182 55 h174 kg_469_2182
    have h176 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2267 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2237 30 h175 kg_469_2237
    have h177 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2272 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2267 5 h176 kg_469_2267
    have h178 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2299 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2272 27 h177 kg_469_2272
    have h179 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2301 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2299 2 h178 kg_469_2299
    have h180 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2313 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2301 12 h179 kg_469_2301
    have h181 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2328 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2313 15 h180 kg_469_2313
    have h182 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2330 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2328 2 h181 kg_469_2328
    have h183 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2342 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2330 12 h182 kg_469_2330
    have h184 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2345 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2342 3 h183 kg_469_2342
    have h185 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2351 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2345 6 h184 kg_469_2345
    have h186 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2354 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2351 3 h185 kg_469_2351
    have h187 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2368 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2354 14 h186 kg_469_2354
    have h188 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2378 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2368 10 h187 kg_469_2368
    have h189 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2381 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2378 3 h188 kg_469_2378
    have h190 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2405 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2381 24 h189 kg_469_2381
    have h191 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2451 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2405 46 h190 kg_469_2405
    have h192 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2460 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2451 9 h191 kg_469_2451
    have h193 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2489 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2460 29 h192 kg_469_2460
    have h194 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2505 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2489 16 h193 kg_469_2489
    have h195 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2507 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2505 2 h194 kg_469_2505
    have h196 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2523 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2507 16 h195 kg_469_2507
    have h197 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2527 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2523 4 h196 kg_469_2523
    have h198 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2550 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2527 23 h197 kg_469_2527
    have h199 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2557 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2550 7 h198 kg_469_2550
    have h200 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2576 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2557 19 h199 kg_469_2557
    have h201 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2601 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2576 25 h200 kg_469_2576
    have h202 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2629 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2601 28 h201 kg_469_2601
    have h203 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2646 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2629 17 h202 kg_469_2629
    have h204 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2702 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2646 56 h203 kg_469_2646
    have h205 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2758 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2702 56 h204 kg_469_2702
    have h206 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2779 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2758 21 h205 kg_469_2758
    have h207 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2781 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2779 2 h206 kg_469_2779
    have h208 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2793 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2781 12 h207 kg_469_2781
    have h209 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2796 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2793 3 h208 kg_469_2793
    have h210 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2802 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2796 6 h209 kg_469_2796
    have h211 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2804 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2802 2 h210 kg_469_2802
    have h212 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2823 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2804 19 h211 kg_469_2804
    have h213 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2825 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2823 2 h212 kg_469_2823
    have h214 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2840 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2825 15 h213 kg_469_2825
    have h215 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2865 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2840 25 h214 kg_469_2840
    have h216 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2876 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2865 11 h215 kg_469_2865
    have h217 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2896 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2876 20 h216 kg_469_2876
    have h218 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 2985 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2896 89 h217 kg_469_2896
    have h219 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3021 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 2985 36 h218 kg_469_2985
    have h220 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3022 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3021 1 h219 kg_469_3021
    have h221 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3031 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3022 9 h220 kg_469_3022
    have h222 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3060 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3031 29 h221 kg_469_3031
    have h223 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3122 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3060 62 h222 kg_469_3060
    have h224 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3139 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3122 17 h223 kg_469_3122
    have h225 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3154 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3139 15 h224 kg_469_3139
    have h226 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3159 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3154 5 h225 kg_469_3154
    have h227 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3182 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3159 23 h226 kg_469_3159
    have h228 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3197 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3182 15 h227 kg_469_3182
    have h229 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3215 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3197 18 h228 kg_469_3197
    have h230 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3267 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3215 52 h229 kg_469_3215
    have h231 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3268 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3267 1 h230 kg_469_3267
    have h232 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3298 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3268 30 h231 kg_469_3268
    have h233 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3299 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3298 1 h232 kg_469_3298
    have h234 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3315 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3299 16 h233 kg_469_3299
    have h235 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3364 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3315 49 h234 kg_469_3315
    have h236 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3370 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3364 6 h235 kg_469_3364
    have h237 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3384 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3370 14 h236 kg_469_3370
    have h238 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3414 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3384 30 h237 kg_469_3384
    have h239 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3431 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3414 17 h238 kg_469_3414
    have h240 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3452 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3431 21 h239 kg_469_3431
    have h241 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3481 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3452 29 h240 kg_469_3452
    have h242 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3488 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3481 7 h241 kg_469_3481
    have h243 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3517 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3488 29 h242 kg_469_3488
    have h244 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3527 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3517 10 h243 kg_469_3517
    have h245 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3611 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3527 84 h244 kg_469_3527
    have h246 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3624 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3611 13 h245 kg_469_3611
    have h247 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3645 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3624 21 h246 kg_469_3624
    have h248 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3664 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3645 19 h247 kg_469_3645
    have h249 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3677 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3664 13 h248 kg_469_3664
    have h250 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3678 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3677 1 h249 kg_469_3677
    have h251 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3708 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3678 30 h250 kg_469_3678
    have h252 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3709 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3708 1 h251 kg_469_3708
    have h253 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3724 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3709 15 h252 kg_469_3709
    have h254 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3752 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3724 28 h253 kg_469_3724
    have h255 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3761 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3752 9 h254 kg_469_3752
    have h256 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3790 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3761 29 h255 kg_469_3761
    have h257 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3796 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3790 6 h256 kg_469_3790
    have h258 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3811 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3796 15 h257 kg_469_3796
    have h259 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3838 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3811 27 h258 kg_469_3811
    have h260 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3864 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3838 26 h259 kg_469_3838
    have h261 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3892 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3864 28 h260 kg_469_3864
    have h262 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3935 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3892 43 h261 kg_469_3892
    have h263 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 3981 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3935 46 h262 kg_469_3935
    have h264 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4038 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 3981 57 h263 kg_469_3981
    have h265 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4043 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4038 5 h264 kg_469_4038
    have h266 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4063 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4043 20 h265 kg_469_4043
    have h267 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4069 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4063 6 h266 kg_469_4063
    have h268 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4082 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4069 13 h267 kg_469_4069
    have h269 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4105 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4082 23 h268 kg_469_4082
    have h270 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4133 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4105 28 h269 kg_469_4105
    have h271 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4154 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4133 21 h270 kg_469_4133
    have h272 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4186 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4154 32 h271 kg_469_4154
    have h273 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4213 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4186 27 h272 kg_469_4186
    have h274 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4214 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4213 1 h273 kg_469_4213
    have h275 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4220 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4214 6 h274 kg_469_4214
    have h276 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4226 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4220 6 h275 kg_469_4220
    have h277 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4243 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4226 17 h276 kg_469_4226
    have h278 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4254 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4243 11 h277 kg_469_4243
    have h279 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4255 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4254 1 h278 kg_469_4254
    have h280 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4262 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4255 7 h279 kg_469_4255
    have h281 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4274 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4262 12 h280 kg_469_4262
    have h282 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4291 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4274 17 h281 kg_469_4274
    have h283 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4295 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4291 4 h282 kg_469_4291
    have h284 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4301 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4295 6 h283 kg_469_4295
    have h285 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4320 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4301 19 h284 kg_469_4301
    have h286 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4376 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4320 56 h285 kg_469_4320
    have h287 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4436 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4376 60 h286 kg_469_4376
    have h288 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4442 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4436 6 h287 kg_469_4436
    have h289 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4464 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4442 22 h288 kg_469_4442
    have h290 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4533 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4464 69 h289 kg_469_4464
    have h291 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4584 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4533 51 h290 kg_469_4533
    have h292 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4607 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4584 23 h291 kg_469_4584
    have h293 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4638 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4607 31 h292 kg_469_4607
    have h294 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4643 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4638 5 h293 kg_469_4638
    have h295 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4644 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4643 1 h294 kg_469_4643
    have h296 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4651 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4644 7 h295 kg_469_4644
    have h297 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4652 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4651 1 h296 kg_469_4651
    have h298 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4662 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4652 10 h297 kg_469_4652
    have h299 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4668 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4662 6 h298 kg_469_4662
    have h300 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4685 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4668 17 h299 kg_469_4668
    have h301 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4741 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4685 56 h300 kg_469_4685
    have h302 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4819 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4741 78 h301 kg_469_4741
    have h303 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4838 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4819 19 h302 kg_469_4819
    have h304 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4841 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4838 3 h303 kg_469_4838
    have h305 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4863 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4841 22 h304 kg_469_4841
    have h306 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4885 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4863 22 h305 kg_469_4863
    have h307 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4912 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4885 27 h306 kg_469_4885
    have h308 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4943 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4912 31 h307 kg_469_4912
    have h309 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4954 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4943 11 h308 kg_469_4943
    have h310 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4955 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4954 1 h309 kg_469_4954
    have h311 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4964 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4955 9 h310 kg_469_4955
    have h312 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4976 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4964 12 h311 kg_469_4964
    have h313 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 4991 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4976 15 h312 kg_469_4976
    have h314 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 5003 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 4991 12 h313 kg_469_4991
    have h315 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 5009 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 5003 6 h314 kg_469_5003
    have h316 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 5035 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 5009 26 h315 kg_469_5009
    have h317 : IPChk.allR (Pts.glueIB K469.lits KW_469) 0 5037 = true := IPChk.allR_join (Pts.glueIB K469.lits KW_469) 0 5035 2 h316 kg_469_5035
    exact h317
  have hlen : K469.lits.length = 5037 := by decide
  intro k h1 h2
  obtain rfl : k = 469 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 469) K469.lits KW_469
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_106 : ∀ k, 470 ≤ k → k < 471 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_470 JW_470 470 1 jr_470
theorem jr6_107 : ∀ k, 471 ≤ k → k < 472 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2551 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2 = true := kb_471_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2 3 h0 kb_471_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 5 4 h1 kb_471_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 9 2 h2 kb_471_9
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 11 8 h3 kb_471_11
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 19 8 h4 kb_471_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 27 6 h5 kb_471_27
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 33 8 h6 kb_471_33
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 41 10 h7 kb_471_41
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 51 8 h8 kb_471_51
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 59 9 h9 kb_471_59
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 68 8 h10 kb_471_68
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 76 9 h11 kb_471_76
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 85 8 h12 kb_471_85
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 93 8 h13 kb_471_93
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 101 2 h14 kb_471_101
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 103 1 h15 kb_471_103
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 104 20 h16 kb_471_104
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 124 11 h17 kb_471_124
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 135 6 h18 kb_471_135
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 141 2 h19 kb_471_141
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 143 22 h20 kb_471_143
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 165 2 h21 kb_471_165
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 167 3 h22 kb_471_167
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 170 6 h23 kb_471_170
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 176 2 h24 kb_471_176
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 178 22 h25 kb_471_178
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 200 1 h26 kb_471_200
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 201 1 h27 kb_471_201
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 202 1 h28 kb_471_202
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 203 8 h29 kb_471_203
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 211 5 h30 kb_471_211
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 216 2 h31 kb_471_216
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 218 33 h32 kb_471_218
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 265 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 251 14 h33 kb_471_251
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 265 18 h34 kb_471_265
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 283 2 h35 kb_471_283
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 285 24 h36 kb_471_285
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 309 2 h37 kb_471_309
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 311 6 h38 kb_471_311
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 317 2 h39 kb_471_317
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 319 19 h40 kb_471_319
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 338 9 h41 kb_471_338
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 347 17 h42 kb_471_347
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 364 6 h43 kb_471_364
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 370 2 h44 kb_471_370
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 372 34 h45 kb_471_372
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 406 19 h46 kb_471_406
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 425 22 h47 kb_471_425
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 447 2 h48 kb_471_447
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 449 16 h49 kb_471_449
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 465 15 h50 kb_471_465
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 480 6 h51 kb_471_480
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 486 2 h52 kb_471_486
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 488 20 h53 kb_471_488
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 508 1 h54 kb_471_508
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 509 2 h55 kb_471_509
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 511 9 h56 kb_471_511
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 520 19 h57 kb_471_520
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 539 1 h58 kb_471_539
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 542 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 540 2 h59 kb_471_540
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 545 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 542 3 h60 kb_471_542
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 545 6 h61 kb_471_545
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 551 33 h62 kb_471_551
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 584 2 h63 kb_471_584
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 586 25 h64 kb_471_586
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 611 5 h65 kb_471_611
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 630 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 616 14 h66 kb_471_616
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 632 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 630 2 h67 kb_471_630
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 632 6 h68 kb_471_632
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 638 2 h69 kb_471_638
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 640 20 h70 kb_471_640
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 660 3 h71 kb_471_660
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 669 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 663 6 h72 kb_471_663
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 671 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 669 2 h73 kb_471_669
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 671 20 h74 kb_471_671
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 691 6 h75 kb_471_691
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 713 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 697 16 h76 kb_471_697
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 713 21 h77 kb_471_713
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 736 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 734 2 h78 kb_471_734
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 736 4 h79 kb_471_736
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 740 23 h80 kb_471_740
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 766 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 763 3 h81 kb_471_763
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 766 1 h82 kb_471_766
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 769 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 767 2 h83 kb_471_767
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 769 18 h84 kb_471_769
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 807 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 787 20 h85 kb_471_787
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 807 4 h86 kb_471_807
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 868 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 811 57 h87 kb_471_811
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 907 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 868 39 h88 kb_471_868
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 909 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 907 2 h89 kb_471_907
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 909 15 h90 kb_471_909
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 930 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 924 6 h91 kb_471_924
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 930 2 h92 kb_471_930
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 952 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 932 20 h93 kb_471_932
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 959 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 952 7 h94 kb_471_952
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 980 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 959 21 h95 kb_471_959
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1009 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 980 29 h96 kb_471_980
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1032 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1009 23 h97 kb_471_1009
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1042 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1032 10 h98 kb_471_1032
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1056 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1042 14 h99 kb_471_1042
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1056 57 h100 kb_471_1056
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1113 25 h101 kb_471_1113
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1138 11 h102 kb_471_1138
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1149 24 h103 kb_471_1149
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1173 2 h104 kb_471_1173
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1175 14 h105 kb_471_1175
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1189 14 h106 kb_471_1189
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1203 2 h107 kb_471_1203
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1205 15 h108 kb_471_1205
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1220 6 h109 kb_471_1220
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1226 2 h110 kb_471_1226
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1228 17 h111 kb_471_1228
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1245 8 h112 kb_471_1245
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1253 2 h113 kb_471_1253
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1255 16 h114 kb_471_1255
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1271 13 h115 kb_471_1271
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1284 2 h116 kb_471_1284
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1286 15 h117 kb_471_1286
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1301 4 h118 kb_471_1301
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1305 8 h119 kb_471_1305
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1313 15 h120 kb_471_1313
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1328 11 h121 kb_471_1328
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1339 77 h122 kb_471_1339
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1416 28 h123 kb_471_1416
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1444 30 h124 kb_471_1444
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1474 18 h125 kb_471_1474
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1492 3 h126 kb_471_1492
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1543 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1495 48 h127 kb_471_1495
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1545 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1543 2 h128 kb_471_1543
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1545 17 h129 kb_471_1545
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1590 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1562 28 h130 kb_471_1562
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1594 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1590 4 h131 kb_471_1590
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1594 28 h132 kb_471_1594
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1622 33 h133 kb_471_1622
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1655 1 h134 kb_471_1655
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1656 24 h135 kb_471_1656
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1680 1 h136 kb_471_1680
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1681 25 h137 kb_471_1681
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1706 90 h138 kb_471_1706
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1796 6 h139 kb_471_1796
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1832 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1802 30 h140 kb_471_1802
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1832 23 h141 kb_471_1832
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1872 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1855 17 h142 kb_471_1855
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1895 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1872 23 h143 kb_471_1872
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1925 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1895 30 h144 kb_471_1895
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1967 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1925 42 h145 kb_471_1925
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2000 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 1967 33 h146 kb_471_1967
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2010 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2000 10 h147 kb_471_2000
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2038 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2010 28 h148 kb_471_2010
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2044 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2038 6 h149 kb_471_2038
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2059 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2044 15 h150 kb_471_2044
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2080 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2059 21 h151 kb_471_2059
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2080 2 h152 kb_471_2080
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2094 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2082 12 h153 kb_471_2082
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2094 19 h154 kb_471_2094
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2113 3 h155 kb_471_2113
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2116 27 h156 kb_471_2116
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2143 20 h157 kb_471_2143
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2163 23 h158 kb_471_2163
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2186 2 h159 kb_471_2186
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2188 31 h160 kb_471_2188
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2219 28 h161 kb_471_2219
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2247 62 h162 kb_471_2247
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2309 63 h163 kb_471_2309
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2372 3 h164 kb_471_2372
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2375 13 h165 kb_471_2375
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2388 1 h166 kb_471_2388
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2389 19 h167 kb_471_2389
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2408 29 h168 kb_471_2408
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2437 18 h169 kb_471_2437
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2455 21 h170 kb_471_2455
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2476 21 h171 kb_471_2476
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2526 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2497 29 h172 kb_471_2497
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2541 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2526 15 h173 kb_471_2526
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K471.lits.getD i 0)) 0 2541 10 h174 kb_471_2541
    exact h175
  have hg : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2551 = true := by
    have h0 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2 = true := kg_471_0
    have h1 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 5 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2 3 h0 kg_471_2
    have h2 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 9 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 5 4 h1 kg_471_5
    have h3 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 11 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 9 2 h2 kg_471_9
    have h4 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 19 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 11 8 h3 kg_471_11
    have h5 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 27 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 19 8 h4 kg_471_19
    have h6 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 33 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 27 6 h5 kg_471_27
    have h7 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 41 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 33 8 h6 kg_471_33
    have h8 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 51 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 41 10 h7 kg_471_41
    have h9 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 59 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 51 8 h8 kg_471_51
    have h10 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 68 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 59 9 h9 kg_471_59
    have h11 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 76 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 68 8 h10 kg_471_68
    have h12 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 85 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 76 9 h11 kg_471_76
    have h13 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 93 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 85 8 h12 kg_471_85
    have h14 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 101 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 93 8 h13 kg_471_93
    have h15 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 103 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 101 2 h14 kg_471_101
    have h16 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 104 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 103 1 h15 kg_471_103
    have h17 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 124 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 104 20 h16 kg_471_104
    have h18 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 135 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 124 11 h17 kg_471_124
    have h19 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 141 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 135 6 h18 kg_471_135
    have h20 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 143 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 141 2 h19 kg_471_141
    have h21 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 165 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 143 22 h20 kg_471_143
    have h22 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 167 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 165 2 h21 kg_471_165
    have h23 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 170 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 167 3 h22 kg_471_167
    have h24 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 176 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 170 6 h23 kg_471_170
    have h25 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 178 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 176 2 h24 kg_471_176
    have h26 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 200 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 178 22 h25 kg_471_178
    have h27 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 201 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 200 1 h26 kg_471_200
    have h28 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 202 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 201 1 h27 kg_471_201
    have h29 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 203 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 202 1 h28 kg_471_202
    have h30 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 211 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 203 8 h29 kg_471_203
    have h31 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 216 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 211 5 h30 kg_471_211
    have h32 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 218 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 216 2 h31 kg_471_216
    have h33 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 251 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 218 33 h32 kg_471_218
    have h34 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 265 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 251 14 h33 kg_471_251
    have h35 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 283 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 265 18 h34 kg_471_265
    have h36 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 285 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 283 2 h35 kg_471_283
    have h37 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 309 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 285 24 h36 kg_471_285
    have h38 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 311 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 309 2 h37 kg_471_309
    have h39 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 317 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 311 6 h38 kg_471_311
    have h40 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 319 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 317 2 h39 kg_471_317
    have h41 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 338 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 319 19 h40 kg_471_319
    have h42 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 347 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 338 9 h41 kg_471_338
    have h43 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 364 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 347 17 h42 kg_471_347
    have h44 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 370 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 364 6 h43 kg_471_364
    have h45 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 372 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 370 2 h44 kg_471_370
    have h46 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 406 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 372 34 h45 kg_471_372
    have h47 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 425 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 406 19 h46 kg_471_406
    have h48 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 447 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 425 22 h47 kg_471_425
    have h49 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 449 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 447 2 h48 kg_471_447
    have h50 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 465 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 449 16 h49 kg_471_449
    have h51 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 480 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 465 15 h50 kg_471_465
    have h52 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 486 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 480 6 h51 kg_471_480
    have h53 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 488 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 486 2 h52 kg_471_486
    have h54 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 508 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 488 20 h53 kg_471_488
    have h55 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 509 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 508 1 h54 kg_471_508
    have h56 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 511 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 509 2 h55 kg_471_509
    have h57 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 520 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 511 9 h56 kg_471_511
    have h58 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 539 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 520 19 h57 kg_471_520
    have h59 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 540 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 539 1 h58 kg_471_539
    have h60 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 542 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 540 2 h59 kg_471_540
    have h61 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 545 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 542 3 h60 kg_471_542
    have h62 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 551 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 545 6 h61 kg_471_545
    have h63 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 584 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 551 33 h62 kg_471_551
    have h64 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 586 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 584 2 h63 kg_471_584
    have h65 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 611 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 586 25 h64 kg_471_586
    have h66 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 616 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 611 5 h65 kg_471_611
    have h67 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 630 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 616 14 h66 kg_471_616
    have h68 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 632 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 630 2 h67 kg_471_630
    have h69 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 638 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 632 6 h68 kg_471_632
    have h70 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 640 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 638 2 h69 kg_471_638
    have h71 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 660 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 640 20 h70 kg_471_640
    have h72 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 663 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 660 3 h71 kg_471_660
    have h73 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 669 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 663 6 h72 kg_471_663
    have h74 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 671 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 669 2 h73 kg_471_669
    have h75 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 691 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 671 20 h74 kg_471_671
    have h76 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 697 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 691 6 h75 kg_471_691
    have h77 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 713 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 697 16 h76 kg_471_697
    have h78 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 734 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 713 21 h77 kg_471_713
    have h79 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 736 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 734 2 h78 kg_471_734
    have h80 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 740 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 736 4 h79 kg_471_736
    have h81 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 763 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 740 23 h80 kg_471_740
    have h82 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 766 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 763 3 h81 kg_471_763
    have h83 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 767 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 766 1 h82 kg_471_766
    have h84 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 769 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 767 2 h83 kg_471_767
    have h85 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 787 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 769 18 h84 kg_471_769
    have h86 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 807 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 787 20 h85 kg_471_787
    have h87 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 811 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 807 4 h86 kg_471_807
    have h88 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 868 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 811 57 h87 kg_471_811
    have h89 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 907 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 868 39 h88 kg_471_868
    have h90 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 909 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 907 2 h89 kg_471_907
    have h91 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 924 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 909 15 h90 kg_471_909
    have h92 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 930 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 924 6 h91 kg_471_924
    have h93 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 932 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 930 2 h92 kg_471_930
    have h94 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 952 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 932 20 h93 kg_471_932
    have h95 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 959 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 952 7 h94 kg_471_952
    have h96 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 980 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 959 21 h95 kg_471_959
    have h97 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1009 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 980 29 h96 kg_471_980
    have h98 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1032 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1009 23 h97 kg_471_1009
    have h99 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1042 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1032 10 h98 kg_471_1032
    have h100 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1056 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1042 14 h99 kg_471_1042
    have h101 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1113 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1056 57 h100 kg_471_1056
    have h102 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1138 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1113 25 h101 kg_471_1113
    have h103 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1149 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1138 11 h102 kg_471_1138
    have h104 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1173 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1149 24 h103 kg_471_1149
    have h105 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1175 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1173 2 h104 kg_471_1173
    have h106 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1189 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1175 14 h105 kg_471_1175
    have h107 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1203 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1189 14 h106 kg_471_1189
    have h108 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1205 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1203 2 h107 kg_471_1203
    have h109 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1220 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1205 15 h108 kg_471_1205
    have h110 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1226 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1220 6 h109 kg_471_1220
    have h111 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1228 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1226 2 h110 kg_471_1226
    have h112 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1245 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1228 17 h111 kg_471_1228
    have h113 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1253 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1245 8 h112 kg_471_1245
    have h114 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1255 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1253 2 h113 kg_471_1253
    have h115 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1271 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1255 16 h114 kg_471_1255
    have h116 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1284 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1271 13 h115 kg_471_1271
    have h117 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1286 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1284 2 h116 kg_471_1284
    have h118 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1301 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1286 15 h117 kg_471_1286
    have h119 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1305 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1301 4 h118 kg_471_1301
    have h120 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1313 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1305 8 h119 kg_471_1305
    have h121 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1328 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1313 15 h120 kg_471_1313
    have h122 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1339 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1328 11 h121 kg_471_1328
    have h123 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1416 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1339 77 h122 kg_471_1339
    have h124 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1444 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1416 28 h123 kg_471_1416
    have h125 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1474 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1444 30 h124 kg_471_1444
    have h126 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1492 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1474 18 h125 kg_471_1474
    have h127 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1495 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1492 3 h126 kg_471_1492
    have h128 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1543 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1495 48 h127 kg_471_1495
    have h129 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1545 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1543 2 h128 kg_471_1543
    have h130 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1562 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1545 17 h129 kg_471_1545
    have h131 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1590 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1562 28 h130 kg_471_1562
    have h132 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1594 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1590 4 h131 kg_471_1590
    have h133 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1622 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1594 28 h132 kg_471_1594
    have h134 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1655 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1622 33 h133 kg_471_1622
    have h135 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1656 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1655 1 h134 kg_471_1655
    have h136 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1680 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1656 24 h135 kg_471_1656
    have h137 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1681 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1680 1 h136 kg_471_1680
    have h138 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1706 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1681 25 h137 kg_471_1681
    have h139 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1796 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1706 90 h138 kg_471_1706
    have h140 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1802 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1796 6 h139 kg_471_1796
    have h141 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1832 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1802 30 h140 kg_471_1802
    have h142 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1855 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1832 23 h141 kg_471_1832
    have h143 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1872 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1855 17 h142 kg_471_1855
    have h144 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1895 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1872 23 h143 kg_471_1872
    have h145 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1925 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1895 30 h144 kg_471_1895
    have h146 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 1967 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1925 42 h145 kg_471_1925
    have h147 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2000 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 1967 33 h146 kg_471_1967
    have h148 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2010 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2000 10 h147 kg_471_2000
    have h149 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2038 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2010 28 h148 kg_471_2010
    have h150 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2044 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2038 6 h149 kg_471_2038
    have h151 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2059 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2044 15 h150 kg_471_2044
    have h152 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2080 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2059 21 h151 kg_471_2059
    have h153 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2082 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2080 2 h152 kg_471_2080
    have h154 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2094 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2082 12 h153 kg_471_2082
    have h155 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2113 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2094 19 h154 kg_471_2094
    have h156 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2116 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2113 3 h155 kg_471_2113
    have h157 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2143 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2116 27 h156 kg_471_2116
    have h158 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2163 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2143 20 h157 kg_471_2143
    have h159 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2186 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2163 23 h158 kg_471_2163
    have h160 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2188 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2186 2 h159 kg_471_2186
    have h161 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2219 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2188 31 h160 kg_471_2188
    have h162 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2247 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2219 28 h161 kg_471_2219
    have h163 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2309 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2247 62 h162 kg_471_2247
    have h164 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2372 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2309 63 h163 kg_471_2309
    have h165 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2375 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2372 3 h164 kg_471_2372
    have h166 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2388 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2375 13 h165 kg_471_2375
    have h167 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2389 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2388 1 h166 kg_471_2388
    have h168 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2408 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2389 19 h167 kg_471_2389
    have h169 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2437 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2408 29 h168 kg_471_2408
    have h170 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2455 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2437 18 h169 kg_471_2437
    have h171 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2476 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2455 21 h170 kg_471_2455
    have h172 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2497 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2476 21 h171 kg_471_2476
    have h173 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2526 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2497 29 h172 kg_471_2497
    have h174 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2541 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2526 15 h173 kg_471_2526
    have h175 : IPChk.allR (Pts.glueIB K471.lits KW_471) 0 2551 = true := IPChk.allR_join (Pts.glueIB K471.lits KW_471) 0 2541 10 h174 kg_471_2541
    exact h175
  have hlen : K471.lits.length = 2551 := by decide
  intro k h1 h2
  obtain rfl : k = 471 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 471) K471.lits KW_471
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_108 : ∀ k, 472 ≤ k → k < 473 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_472 JW_472 472 1 jr_472

theorem grp6_4 : ∀ k, 393 ≤ k → k < 473 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_88
  have a1 := Pts.fa_join a0 jr6_89
  have a2 := Pts.fa_join a1 jr6_90
  have a3 := Pts.fa_join a2 jr6_91
  have a4 := Pts.fa_join a3 jr6_92
  have a5 := Pts.fa_join a4 jr6_93
  have a6 := Pts.fa_join a5 jr6_94
  have a7 := Pts.fa_join a6 jr6_95
  have a8 := Pts.fa_join a7 jr6_96
  have a9 := Pts.fa_join a8 jr6_97
  have a10 := Pts.fa_join a9 jr6_98
  have a11 := Pts.fa_join a10 jr6_99
  have a12 := Pts.fa_join a11 jr6_100
  have a13 := Pts.fa_join a12 jr6_101
  have a14 := Pts.fa_join a13 jr6_102
  have a15 := Pts.fa_join a14 jr6_103
  have a16 := Pts.fa_join a15 jr6_104
  have a17 := Pts.fa_join a16 jr6_105
  have a18 := Pts.fa_join a17 jr6_106
  have a19 := Pts.fa_join a18 jr6_107
  have a20 := Pts.fa_join a19 jr6_108
  exact a20

end B334.E1x.Pts.S707
