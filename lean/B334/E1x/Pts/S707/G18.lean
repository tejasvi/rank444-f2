import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J3023
import B334.E1x.Pts.S707.J3027
import B334.E1x.Pts.S707.J3031
import B334.E1x.Pts.S707.J3033
import B334.E1x.Pts.S707.J3041
import B334.E1x.Pts.S707.J3049
import B334.E1x.Pts.S707.J3078
import B334.E1x.Pts.S707.K3022L
import B334.E1x.Pts.S707.K3025L
import B334.E1x.Pts.S707.K3026L
import B334.E1x.Pts.S707.K3029L
import B334.E1x.Pts.S707.K3030L
import B334.E1x.Pts.S707.K3032L
import B334.E1x.Pts.S707.K3040L
import B334.E1x.Pts.S707.K3048L
import B334.E1x.Pts.S707.K3077L
import B334.E1x.Pts.S707.K3079L
import B334.E1x.Pts.S707.K3022Q0
import B334.E1x.Pts.S707.K3022Q1
import B334.E1x.Pts.S707.K3022Q2
import B334.E1x.Pts.S707.K3022Q3
import B334.E1x.Pts.S707.K3022Q4
import B334.E1x.Pts.S707.K3022Q5
import B334.E1x.Pts.S707.K3022Q6
import B334.E1x.Pts.S707.K3022Q7
import B334.E1x.Pts.S707.K3022Q8
import B334.E1x.Pts.S707.K3022Q9
import B334.E1x.Pts.S707.K3025Q0
import B334.E1x.Pts.S707.K3025Q1
import B334.E1x.Pts.S707.K3025Q2
import B334.E1x.Pts.S707.K3025Q3
import B334.E1x.Pts.S707.K3025Q4
import B334.E1x.Pts.S707.K3025Q5
import B334.E1x.Pts.S707.K3025Q6
import B334.E1x.Pts.S707.K3025Q7
import B334.E1x.Pts.S707.K3026Q0
import B334.E1x.Pts.S707.K3026Q1
import B334.E1x.Pts.S707.K3029Q0
import B334.E1x.Pts.S707.K3029Q1
import B334.E1x.Pts.S707.K3029Q2
import B334.E1x.Pts.S707.K3030Q0
import B334.E1x.Pts.S707.K3030Q1
import B334.E1x.Pts.S707.K3032Q0
import B334.E1x.Pts.S707.K3032Q1
import B334.E1x.Pts.S707.K3032Q2
import B334.E1x.Pts.S707.K3032Q3
import B334.E1x.Pts.S707.K3032Q4
import B334.E1x.Pts.S707.K3040Q0
import B334.E1x.Pts.S707.K3048Q0
import B334.E1x.Pts.S707.K3077Q0
import B334.E1x.Pts.S707.K3077Q1
import B334.E1x.Pts.S707.K3077Q2
import B334.E1x.Pts.S707.K3077Q3
import B334.E1x.Pts.S707.K3077Q4
import B334.E1x.Pts.S707.K3077Q5
import B334.E1x.Pts.S707.K3077Q6
import B334.E1x.Pts.S707.K3077Q7
import B334.E1x.Pts.S707.K3077Q8
import B334.E1x.Pts.S707.K3077Q9
import B334.E1x.Pts.S707.K3079Q0
import B334.E1x.Pts.S707.K3079Q1
import B334.E1x.Pts.S707.K3022Q10
import B334.E1x.Pts.S707.K3022Q11
import B334.E1x.Pts.S707.K3022Q12
import B334.E1x.Pts.S707.K3022Q13
import B334.E1x.Pts.S707.K3022Q14
import B334.E1x.Pts.S707.K3022Q15
import B334.E1x.Pts.S707.K3022Q16
import B334.E1x.Pts.S707.K3022Q17
import B334.E1x.Pts.S707.K3022Q18
import B334.E1x.Pts.S707.K3022Q19
import B334.E1x.Pts.S707.K3022Q20
import B334.E1x.Pts.S707.K3022Q21
import B334.E1x.Pts.S707.K3022Q22
import B334.E1x.Pts.S707.K3022Q23
import B334.E1x.Pts.S707.K3022Q24
import B334.E1x.Pts.S707.K3022Q25
import B334.E1x.Pts.S707.K3077Q10
import B334.E1x.Pts.S707.K3077Q11
import B334.E1x.Pts.S707.K3077Q12
import B334.E1x.Pts.S707.K3077Q13
import B334.E1x.Pts.S707.K3077Q14
import B334.E1x.Pts.S707.K3077Q15

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 3022 … 3079 (stage707_v6): the v5 Fin's job blocks r529 … r545 as
theorems, joined into `grp6_18` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_529 : ∀ k, 3022 ≤ k → k < 3023 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2282 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2 = true := kb_3022_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2 1 h0 kb_3022_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 3 4 h1 kb_3022_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 7 2 h2 kb_3022_7
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 9 8 h3 kb_3022_9
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 17 7 h4 kb_3022_17
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 24 2 h5 kb_3022_24
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 26 3 h6 kb_3022_26
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 29 3 h7 kb_3022_29
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 32 9 h8 kb_3022_32
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 41 4 h9 kb_3022_41
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 45 7 h10 kb_3022_45
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 52 8 h11 kb_3022_52
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 60 7 h12 kb_3022_60
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 67 5 h13 kb_3022_67
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 72 6 h14 kb_3022_72
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 78 1 h15 kb_3022_78
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 79 1 h16 kb_3022_79
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 80 21 h17 kb_3022_80
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 101 2 h18 kb_3022_101
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 103 6 h19 kb_3022_103
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 109 2 h20 kb_3022_109
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 111 16 h21 kb_3022_111
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 127 2 h22 kb_3022_127
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 129 3 h23 kb_3022_129
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 132 6 h24 kb_3022_132
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 138 4 h25 kb_3022_138
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 142 15 h26 kb_3022_142
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 157 1 h27 kb_3022_157
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 158 1 h28 kb_3022_158
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 159 1 h29 kb_3022_159
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 160 7 h30 kb_3022_160
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 167 2 h31 kb_3022_167
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 169 6 h32 kb_3022_169
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 175 2 h33 kb_3022_175
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 177 2 h34 kb_3022_177
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 179 1 h35 kb_3022_179
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 180 1 h36 kb_3022_180
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 181 29 h37 kb_3022_181
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 210 2 h38 kb_3022_210
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 212 6 h39 kb_3022_212
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 218 2 h40 kb_3022_218
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 220 22 h41 kb_3022_220
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 242 9 h42 kb_3022_242
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 251 34 h43 kb_3022_251
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 285 5 h44 kb_3022_285
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 290 8 h45 kb_3022_290
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 298 7 h46 kb_3022_298
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 305 1 h47 kb_3022_305
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 306 3 h48 kb_3022_306
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 309 1 h49 kb_3022_309
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 310 1 h50 kb_3022_310
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 311 21 h51 kb_3022_311
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 332 10 h52 kb_3022_332
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 342 6 h53 kb_3022_342
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 348 2 h54 kb_3022_348
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 350 22 h55 kb_3022_350
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 372 41 h56 kb_3022_372
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 413 8 h57 kb_3022_413
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 421 2 h58 kb_3022_421
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 423 1 h59 kb_3022_423
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 424 5 h60 kb_3022_424
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 429 2 h61 kb_3022_429
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 431 36 h62 kb_3022_431
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 467 17 h63 kb_3022_467
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 484 2 h64 kb_3022_484
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 486 17 h65 kb_3022_486
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 503 1 h66 kb_3022_503
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 504 4 h67 kb_3022_504
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 508 1 h68 kb_3022_508
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 509 9 h69 kb_3022_509
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 518 6 h70 kb_3022_518
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 524 9 h71 kb_3022_524
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 533 2 h72 kb_3022_533
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 535 3 h73 kb_3022_535
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 538 25 h74 kb_3022_538
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 563 23 h75 kb_3022_563
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 586 2 h76 kb_3022_586
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 588 12 h77 kb_3022_588
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 600 2 h78 kb_3022_600
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 602 6 h79 kb_3022_602
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 608 2 h80 kb_3022_608
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 625 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 610 15 h81 kb_3022_610
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 625 8 h82 kb_3022_625
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 633 2 h83 kb_3022_633
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 651 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 635 16 h84 kb_3022_635
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 651 2 h85 kb_3022_651
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 653 13 h86 kb_3022_653
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 671 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 666 5 h87 kb_3022_666
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 671 16 h88 kb_3022_671
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 703 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 687 16 h89 kb_3022_687
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 705 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 703 2 h90 kb_3022_703
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 705 2 h91 kb_3022_705
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 708 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 707 1 h92 kb_3022_707
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 729 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 708 21 h93 kb_3022_708
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 729 10 h94 kb_3022_729
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 745 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 739 6 h95 kb_3022_739
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 747 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 745 2 h96 kb_3022_745
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 776 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 747 29 h97 kb_3022_747
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 776 44 h98 kb_3022_776
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 820 2 h99 kb_3022_820
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 822 4 h100 kb_3022_822
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 826 1 h101 kb_3022_826
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 827 2 h102 kb_3022_827
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 839 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 829 10 h103 kb_3022_829
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 861 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 839 22 h104 kb_3022_839
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 861 6 h105 kb_3022_861
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 867 2 h106 kb_3022_867
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 869 67 h107 kb_3022_869
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 945 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 936 9 h108 kb_3022_936
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 946 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 945 1 h109 kb_3022_945
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 957 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 946 11 h110 kb_3022_946
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 957 21 h111 kb_3022_957
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 984 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 978 6 h112 kb_3022_978
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 986 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 984 2 h113 kb_3022_984
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1053 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 986 67 h114 kb_3022_986
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1053 15 h115 kb_3022_1053
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1070 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1068 2 h116 kb_3022_1068
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1081 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1070 11 h117 kb_3022_1070
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1081 1 h118 kb_3022_1081
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1093 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1082 11 h119 kb_3022_1082
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1094 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1093 1 h120 kb_3022_1093
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1099 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1094 5 h121 kb_3022_1094
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1099 1 h122 kb_3022_1099
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1100 11 h123 kb_3022_1100
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1111 6 h124 kb_3022_1111
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1117 1 h125 kb_3022_1117
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1118 11 h126 kb_3022_1118
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1129 1 h127 kb_3022_1129
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1130 7 h128 kb_3022_1130
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1137 8 h129 kb_3022_1137
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1145 5 h130 kb_3022_1145
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1150 9 h131 kb_3022_1150
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1159 3 h132 kb_3022_1159
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1162 4 h133 kb_3022_1162
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1166 1 h134 kb_3022_1166
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1167 11 h135 kb_3022_1167
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1178 15 h136 kb_3022_1178
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1193 1 h137 kb_3022_1193
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1194 9 h138 kb_3022_1194
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1203 2 h139 kb_3022_1203
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1205 5 h140 kb_3022_1205
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1210 4 h141 kb_3022_1210
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1214 7 h142 kb_3022_1214
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1221 2 h143 kb_3022_1221
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1223 29 h144 kb_3022_1223
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1252 2 h145 kb_3022_1252
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1254 6 h146 kb_3022_1254
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1260 8 h147 kb_3022_1260
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1268 72 h148 kb_3022_1268
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1340 1 h149 kb_3022_1340
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1341 2 h150 kb_3022_1341
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1343 32 h151 kb_3022_1343
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1375 17 h152 kb_3022_1375
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1392 1 h153 kb_3022_1392
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1393 11 h154 kb_3022_1393
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1404 12 h155 kb_3022_1404
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1416 1 h156 kb_3022_1416
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1417 5 h157 kb_3022_1417
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1422 3 h158 kb_3022_1422
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1426 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1425 1 h159 kb_3022_1425
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1426 8 h160 kb_3022_1426
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1435 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1434 1 h161 kb_3022_1434
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1440 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1435 5 h162 kb_3022_1435
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1440 6 h163 kb_3022_1440
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1446 20 h164 kb_3022_1446
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1466 15 h165 kb_3022_1466
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1481 6 h166 kb_3022_1481
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1487 50 h167 kb_3022_1487
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1537 46 h168 kb_3022_1537
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1595 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1583 12 h169 kb_3022_1583
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1595 7 h170 kb_3022_1595
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1615 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1602 13 h171 kb_3022_1602
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1615 9 h172 kb_3022_1615
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1624 5 h173 kb_3022_1624
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1630 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1629 1 h174 kb_3022_1629
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1641 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1630 11 h175 kb_3022_1630
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1641 12 h176 kb_3022_1641
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1653 5 h177 kb_3022_1653
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1658 18 h178 kb_3022_1658
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1676 1 h179 kb_3022_1676
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1677 1 h180 kb_3022_1677
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1678 2 h181 kb_3022_1678
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1680 1 h182 kb_3022_1680
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1681 1 h183 kb_3022_1681
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1682 1 h184 kb_3022_1682
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1683 2 h185 kb_3022_1683
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1685 1 h186 kb_3022_1685
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1686 6 h187 kb_3022_1686
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1698 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1692 6 h188 kb_3022_1692
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1698 3 h189 kb_3022_1698
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1701 5 h190 kb_3022_1701
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1706 1 h191 kb_3022_1706
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1708 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1707 1 h192 kb_3022_1707
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1710 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1708 2 h193 kb_3022_1708
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1711 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1710 1 h194 kb_3022_1710
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1712 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1711 1 h195 kb_3022_1711
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1712 3 h196 kb_3022_1712
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1715 1 h197 kb_3022_1715
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1716 3 h198 kb_3022_1716
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1725 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1719 6 h199 kb_3022_1719
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1725 5 h200 kb_3022_1725
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1730 1 h201 kb_3022_1730
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1731 3 h202 kb_3022_1731
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1734 1 h203 kb_3022_1734
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1736 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1735 1 h204 kb_3022_1735
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1737 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1736 1 h205 kb_3022_1736
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1738 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1737 1 h206 kb_3022_1737
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1738 1 h207 kb_3022_1738
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1739 1 h208 kb_3022_1739
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1740 1 h209 kb_3022_1740
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1745 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1741 4 h210 kb_3022_1741
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1752 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1745 7 h211 kb_3022_1745
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1752 5 h212 kb_3022_1752
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1764 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1757 7 h213 kb_3022_1757
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1769 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1764 5 h214 kb_3022_1764
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1772 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1769 3 h215 kb_3022_1769
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1774 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1772 2 h216 kb_3022_1772
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1774 1 h217 kb_3022_1774
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1775 8 h218 kb_3022_1775
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1783 1 h219 kb_3022_1783
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1784 3 h220 kb_3022_1784
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1787 6 h221 kb_3022_1787
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1793 1 h222 kb_3022_1793
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1795 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1794 1 h223 kb_3022_1794
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1795 2 h224 kb_3022_1795
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1797 29 h225 kb_3022_1797
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1826 2 h226 kb_3022_1826
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1828 6 h227 kb_3022_1828
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1834 8 h228 kb_3022_1834
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1911 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1842 69 h229 kb_3022_1842
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1911 10 h230 kb_3022_1911
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1921 1 h231 kb_3022_1921
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1922 2 h232 kb_3022_1922
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1926 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1924 2 h233 kb_3022_1924
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1926 1 h234 kb_3022_1926
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1929 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1927 2 h235 kb_3022_1927
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1929 34 h236 kb_3022_1929
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2050 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 1963 87 h237 kb_3022_1963
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2079 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2050 29 h238 kb_3022_2050
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2081 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2079 2 h239 kb_3022_2079
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2087 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2081 6 h240 kb_3022_2081
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2093 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2087 6 h241 kb_3022_2087
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2093 74 h242 kb_3022_2093
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2167 3 h243 kb_3022_2167
    have h245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2170 1 h244 kb_3022_2170
    have h246 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2171 1 h245 kb_3022_2171
    have h247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2172 3 h246 kb_3022_2172
    have h248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2175 2 h247 kb_3022_2175
    have h249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2177 32 h248 kb_3022_2177
    have h250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2209 20 h249 kb_3022_2209
    have h251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2229 1 h250 kb_3022_2229
    have h252 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2230 1 h251 kb_3022_2230
    have h253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2231 1 h252 kb_3022_2231
    have h254 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2232 2 h253 kb_3022_2232
    have h255 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2234 1 h254 kb_3022_2234
    have h256 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2235 4 h255 kb_3022_2235
    have h257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2239 1 h256 kb_3022_2239
    have h258 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2240 1 h257 kb_3022_2240
    have h259 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2241 1 h258 kb_3022_2241
    have h260 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2242 2 h259 kb_3022_2242
    have h261 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2244 2 h260 kb_3022_2244
    have h262 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2246 4 h261 kb_3022_2246
    have h263 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2250 1 h262 kb_3022_2250
    have h264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2251 2 h263 kb_3022_2251
    have h265 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2253 7 h264 kb_3022_2253
    have h266 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2266 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2260 6 h265 kb_3022_2260
    have h267 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2266 1 h266 kb_3022_2266
    have h268 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2267 2 h267 kb_3022_2267
    have h269 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2269 3 h268 kb_3022_2269
    have h270 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2272 2 h269 kb_3022_2272
    have h271 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2274 2 h270 kb_3022_2274
    have h272 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2276 3 h271 kb_3022_2276
    have h273 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2279 2 h272 kb_3022_2279
    have h274 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3022.lits.getD i 0)) 0 2281 1 h273 kb_3022_2281
    exact h274
  have hg : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2282 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2 = true := kg_3022_0
    have h1 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 3 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2 1 h0 kg_3022_2
    have h2 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 7 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 3 4 h1 kg_3022_3
    have h3 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 9 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 7 2 h2 kg_3022_7
    have h4 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 17 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 9 8 h3 kg_3022_9
    have h5 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 24 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 17 7 h4 kg_3022_17
    have h6 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 26 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 24 2 h5 kg_3022_24
    have h7 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 29 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 26 3 h6 kg_3022_26
    have h8 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 32 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 29 3 h7 kg_3022_29
    have h9 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 41 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 32 9 h8 kg_3022_32
    have h10 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 45 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 41 4 h9 kg_3022_41
    have h11 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 52 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 45 7 h10 kg_3022_45
    have h12 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 60 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 52 8 h11 kg_3022_52
    have h13 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 67 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 60 7 h12 kg_3022_60
    have h14 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 72 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 67 5 h13 kg_3022_67
    have h15 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 78 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 72 6 h14 kg_3022_72
    have h16 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 79 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 78 1 h15 kg_3022_78
    have h17 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 80 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 79 1 h16 kg_3022_79
    have h18 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 101 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 80 21 h17 kg_3022_80
    have h19 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 103 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 101 2 h18 kg_3022_101
    have h20 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 109 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 103 6 h19 kg_3022_103
    have h21 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 111 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 109 2 h20 kg_3022_109
    have h22 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 127 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 111 16 h21 kg_3022_111
    have h23 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 129 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 127 2 h22 kg_3022_127
    have h24 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 132 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 129 3 h23 kg_3022_129
    have h25 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 138 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 132 6 h24 kg_3022_132
    have h26 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 142 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 138 4 h25 kg_3022_138
    have h27 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 157 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 142 15 h26 kg_3022_142
    have h28 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 158 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 157 1 h27 kg_3022_157
    have h29 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 159 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 158 1 h28 kg_3022_158
    have h30 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 160 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 159 1 h29 kg_3022_159
    have h31 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 167 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 160 7 h30 kg_3022_160
    have h32 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 169 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 167 2 h31 kg_3022_167
    have h33 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 175 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 169 6 h32 kg_3022_169
    have h34 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 177 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 175 2 h33 kg_3022_175
    have h35 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 179 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 177 2 h34 kg_3022_177
    have h36 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 180 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 179 1 h35 kg_3022_179
    have h37 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 181 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 180 1 h36 kg_3022_180
    have h38 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 210 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 181 29 h37 kg_3022_181
    have h39 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 212 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 210 2 h38 kg_3022_210
    have h40 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 218 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 212 6 h39 kg_3022_212
    have h41 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 220 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 218 2 h40 kg_3022_218
    have h42 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 242 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 220 22 h41 kg_3022_220
    have h43 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 251 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 242 9 h42 kg_3022_242
    have h44 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 285 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 251 34 h43 kg_3022_251
    have h45 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 290 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 285 5 h44 kg_3022_285
    have h46 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 298 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 290 8 h45 kg_3022_290
    have h47 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 305 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 298 7 h46 kg_3022_298
    have h48 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 306 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 305 1 h47 kg_3022_305
    have h49 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 309 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 306 3 h48 kg_3022_306
    have h50 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 310 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 309 1 h49 kg_3022_309
    have h51 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 311 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 310 1 h50 kg_3022_310
    have h52 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 332 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 311 21 h51 kg_3022_311
    have h53 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 342 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 332 10 h52 kg_3022_332
    have h54 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 348 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 342 6 h53 kg_3022_342
    have h55 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 350 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 348 2 h54 kg_3022_348
    have h56 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 372 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 350 22 h55 kg_3022_350
    have h57 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 413 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 372 41 h56 kg_3022_372
    have h58 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 421 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 413 8 h57 kg_3022_413
    have h59 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 423 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 421 2 h58 kg_3022_421
    have h60 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 424 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 423 1 h59 kg_3022_423
    have h61 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 429 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 424 5 h60 kg_3022_424
    have h62 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 431 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 429 2 h61 kg_3022_429
    have h63 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 467 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 431 36 h62 kg_3022_431
    have h64 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 484 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 467 17 h63 kg_3022_467
    have h65 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 486 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 484 2 h64 kg_3022_484
    have h66 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 503 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 486 17 h65 kg_3022_486
    have h67 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 504 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 503 1 h66 kg_3022_503
    have h68 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 508 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 504 4 h67 kg_3022_504
    have h69 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 509 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 508 1 h68 kg_3022_508
    have h70 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 518 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 509 9 h69 kg_3022_509
    have h71 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 524 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 518 6 h70 kg_3022_518
    have h72 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 533 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 524 9 h71 kg_3022_524
    have h73 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 535 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 533 2 h72 kg_3022_533
    have h74 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 538 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 535 3 h73 kg_3022_535
    have h75 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 563 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 538 25 h74 kg_3022_538
    have h76 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 586 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 563 23 h75 kg_3022_563
    have h77 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 588 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 586 2 h76 kg_3022_586
    have h78 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 600 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 588 12 h77 kg_3022_588
    have h79 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 602 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 600 2 h78 kg_3022_600
    have h80 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 608 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 602 6 h79 kg_3022_602
    have h81 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 610 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 608 2 h80 kg_3022_608
    have h82 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 625 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 610 15 h81 kg_3022_610
    have h83 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 633 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 625 8 h82 kg_3022_625
    have h84 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 635 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 633 2 h83 kg_3022_633
    have h85 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 651 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 635 16 h84 kg_3022_635
    have h86 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 653 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 651 2 h85 kg_3022_651
    have h87 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 666 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 653 13 h86 kg_3022_653
    have h88 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 671 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 666 5 h87 kg_3022_666
    have h89 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 687 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 671 16 h88 kg_3022_671
    have h90 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 703 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 687 16 h89 kg_3022_687
    have h91 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 705 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 703 2 h90 kg_3022_703
    have h92 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 707 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 705 2 h91 kg_3022_705
    have h93 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 708 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 707 1 h92 kg_3022_707
    have h94 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 729 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 708 21 h93 kg_3022_708
    have h95 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 739 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 729 10 h94 kg_3022_729
    have h96 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 745 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 739 6 h95 kg_3022_739
    have h97 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 747 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 745 2 h96 kg_3022_745
    have h98 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 776 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 747 29 h97 kg_3022_747
    have h99 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 820 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 776 44 h98 kg_3022_776
    have h100 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 822 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 820 2 h99 kg_3022_820
    have h101 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 826 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 822 4 h100 kg_3022_822
    have h102 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 827 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 826 1 h101 kg_3022_826
    have h103 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 829 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 827 2 h102 kg_3022_827
    have h104 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 839 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 829 10 h103 kg_3022_829
    have h105 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 861 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 839 22 h104 kg_3022_839
    have h106 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 867 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 861 6 h105 kg_3022_861
    have h107 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 869 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 867 2 h106 kg_3022_867
    have h108 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 936 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 869 67 h107 kg_3022_869
    have h109 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 945 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 936 9 h108 kg_3022_936
    have h110 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 946 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 945 1 h109 kg_3022_945
    have h111 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 957 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 946 11 h110 kg_3022_946
    have h112 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 978 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 957 21 h111 kg_3022_957
    have h113 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 984 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 978 6 h112 kg_3022_978
    have h114 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 986 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 984 2 h113 kg_3022_984
    have h115 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1053 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 986 67 h114 kg_3022_986
    have h116 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1068 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1053 15 h115 kg_3022_1053
    have h117 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1070 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1068 2 h116 kg_3022_1068
    have h118 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1081 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1070 11 h117 kg_3022_1070
    have h119 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1082 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1081 1 h118 kg_3022_1081
    have h120 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1093 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1082 11 h119 kg_3022_1082
    have h121 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1094 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1093 1 h120 kg_3022_1093
    have h122 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1099 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1094 5 h121 kg_3022_1094
    have h123 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1100 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1099 1 h122 kg_3022_1099
    have h124 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1111 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1100 11 h123 kg_3022_1100
    have h125 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1117 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1111 6 h124 kg_3022_1111
    have h126 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1118 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1117 1 h125 kg_3022_1117
    have h127 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1129 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1118 11 h126 kg_3022_1118
    have h128 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1130 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1129 1 h127 kg_3022_1129
    have h129 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1137 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1130 7 h128 kg_3022_1130
    have h130 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1145 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1137 8 h129 kg_3022_1137
    have h131 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1150 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1145 5 h130 kg_3022_1145
    have h132 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1159 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1150 9 h131 kg_3022_1150
    have h133 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1162 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1159 3 h132 kg_3022_1159
    have h134 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1166 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1162 4 h133 kg_3022_1162
    have h135 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1167 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1166 1 h134 kg_3022_1166
    have h136 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1178 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1167 11 h135 kg_3022_1167
    have h137 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1193 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1178 15 h136 kg_3022_1178
    have h138 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1194 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1193 1 h137 kg_3022_1193
    have h139 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1203 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1194 9 h138 kg_3022_1194
    have h140 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1205 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1203 2 h139 kg_3022_1203
    have h141 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1210 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1205 5 h140 kg_3022_1205
    have h142 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1214 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1210 4 h141 kg_3022_1210
    have h143 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1221 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1214 7 h142 kg_3022_1214
    have h144 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1223 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1221 2 h143 kg_3022_1221
    have h145 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1252 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1223 29 h144 kg_3022_1223
    have h146 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1254 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1252 2 h145 kg_3022_1252
    have h147 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1260 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1254 6 h146 kg_3022_1254
    have h148 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1268 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1260 8 h147 kg_3022_1260
    have h149 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1340 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1268 72 h148 kg_3022_1268
    have h150 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1341 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1340 1 h149 kg_3022_1340
    have h151 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1343 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1341 2 h150 kg_3022_1341
    have h152 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1375 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1343 32 h151 kg_3022_1343
    have h153 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1392 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1375 17 h152 kg_3022_1375
    have h154 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1393 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1392 1 h153 kg_3022_1392
    have h155 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1404 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1393 11 h154 kg_3022_1393
    have h156 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1416 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1404 12 h155 kg_3022_1404
    have h157 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1417 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1416 1 h156 kg_3022_1416
    have h158 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1422 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1417 5 h157 kg_3022_1417
    have h159 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1425 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1422 3 h158 kg_3022_1422
    have h160 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1426 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1425 1 h159 kg_3022_1425
    have h161 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1434 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1426 8 h160 kg_3022_1426
    have h162 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1435 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1434 1 h161 kg_3022_1434
    have h163 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1440 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1435 5 h162 kg_3022_1435
    have h164 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1446 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1440 6 h163 kg_3022_1440
    have h165 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1466 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1446 20 h164 kg_3022_1446
    have h166 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1481 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1466 15 h165 kg_3022_1466
    have h167 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1487 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1481 6 h166 kg_3022_1481
    have h168 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1537 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1487 50 h167 kg_3022_1487
    have h169 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1583 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1537 46 h168 kg_3022_1537
    have h170 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1595 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1583 12 h169 kg_3022_1583
    have h171 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1602 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1595 7 h170 kg_3022_1595
    have h172 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1615 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1602 13 h171 kg_3022_1602
    have h173 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1624 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1615 9 h172 kg_3022_1615
    have h174 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1629 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1624 5 h173 kg_3022_1624
    have h175 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1630 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1629 1 h174 kg_3022_1629
    have h176 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1641 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1630 11 h175 kg_3022_1630
    have h177 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1653 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1641 12 h176 kg_3022_1641
    have h178 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1658 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1653 5 h177 kg_3022_1653
    have h179 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1676 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1658 18 h178 kg_3022_1658
    have h180 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1677 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1676 1 h179 kg_3022_1676
    have h181 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1678 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1677 1 h180 kg_3022_1677
    have h182 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1680 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1678 2 h181 kg_3022_1678
    have h183 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1681 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1680 1 h182 kg_3022_1680
    have h184 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1682 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1681 1 h183 kg_3022_1681
    have h185 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1683 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1682 1 h184 kg_3022_1682
    have h186 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1685 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1683 2 h185 kg_3022_1683
    have h187 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1686 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1685 1 h186 kg_3022_1685
    have h188 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1692 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1686 6 h187 kg_3022_1686
    have h189 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1698 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1692 6 h188 kg_3022_1692
    have h190 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1701 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1698 3 h189 kg_3022_1698
    have h191 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1706 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1701 5 h190 kg_3022_1701
    have h192 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1707 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1706 1 h191 kg_3022_1706
    have h193 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1708 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1707 1 h192 kg_3022_1707
    have h194 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1710 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1708 2 h193 kg_3022_1708
    have h195 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1711 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1710 1 h194 kg_3022_1710
    have h196 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1712 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1711 1 h195 kg_3022_1711
    have h197 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1715 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1712 3 h196 kg_3022_1712
    have h198 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1716 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1715 1 h197 kg_3022_1715
    have h199 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1719 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1716 3 h198 kg_3022_1716
    have h200 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1725 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1719 6 h199 kg_3022_1719
    have h201 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1730 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1725 5 h200 kg_3022_1725
    have h202 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1731 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1730 1 h201 kg_3022_1730
    have h203 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1734 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1731 3 h202 kg_3022_1731
    have h204 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1735 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1734 1 h203 kg_3022_1734
    have h205 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1736 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1735 1 h204 kg_3022_1735
    have h206 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1737 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1736 1 h205 kg_3022_1736
    have h207 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1738 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1737 1 h206 kg_3022_1737
    have h208 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1739 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1738 1 h207 kg_3022_1738
    have h209 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1740 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1739 1 h208 kg_3022_1739
    have h210 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1741 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1740 1 h209 kg_3022_1740
    have h211 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1745 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1741 4 h210 kg_3022_1741
    have h212 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1752 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1745 7 h211 kg_3022_1745
    have h213 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1757 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1752 5 h212 kg_3022_1752
    have h214 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1764 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1757 7 h213 kg_3022_1757
    have h215 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1769 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1764 5 h214 kg_3022_1764
    have h216 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1772 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1769 3 h215 kg_3022_1769
    have h217 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1774 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1772 2 h216 kg_3022_1772
    have h218 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1775 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1774 1 h217 kg_3022_1774
    have h219 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1783 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1775 8 h218 kg_3022_1775
    have h220 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1784 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1783 1 h219 kg_3022_1783
    have h221 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1787 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1784 3 h220 kg_3022_1784
    have h222 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1793 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1787 6 h221 kg_3022_1787
    have h223 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1794 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1793 1 h222 kg_3022_1793
    have h224 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1795 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1794 1 h223 kg_3022_1794
    have h225 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1797 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1795 2 h224 kg_3022_1795
    have h226 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1826 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1797 29 h225 kg_3022_1797
    have h227 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1828 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1826 2 h226 kg_3022_1826
    have h228 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1834 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1828 6 h227 kg_3022_1828
    have h229 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1842 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1834 8 h228 kg_3022_1834
    have h230 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1911 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1842 69 h229 kg_3022_1842
    have h231 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1921 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1911 10 h230 kg_3022_1911
    have h232 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1922 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1921 1 h231 kg_3022_1921
    have h233 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1924 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1922 2 h232 kg_3022_1922
    have h234 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1926 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1924 2 h233 kg_3022_1924
    have h235 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1927 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1926 1 h234 kg_3022_1926
    have h236 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1929 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1927 2 h235 kg_3022_1927
    have h237 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 1963 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1929 34 h236 kg_3022_1929
    have h238 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2050 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 1963 87 h237 kg_3022_1963
    have h239 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2079 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2050 29 h238 kg_3022_2050
    have h240 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2081 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2079 2 h239 kg_3022_2079
    have h241 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2087 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2081 6 h240 kg_3022_2081
    have h242 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2093 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2087 6 h241 kg_3022_2087
    have h243 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2167 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2093 74 h242 kg_3022_2093
    have h244 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2170 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2167 3 h243 kg_3022_2167
    have h245 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2171 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2170 1 h244 kg_3022_2170
    have h246 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2172 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2171 1 h245 kg_3022_2171
    have h247 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2175 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2172 3 h246 kg_3022_2172
    have h248 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2177 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2175 2 h247 kg_3022_2175
    have h249 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2209 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2177 32 h248 kg_3022_2177
    have h250 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2229 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2209 20 h249 kg_3022_2209
    have h251 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2230 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2229 1 h250 kg_3022_2229
    have h252 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2231 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2230 1 h251 kg_3022_2230
    have h253 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2232 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2231 1 h252 kg_3022_2231
    have h254 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2234 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2232 2 h253 kg_3022_2232
    have h255 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2235 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2234 1 h254 kg_3022_2234
    have h256 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2239 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2235 4 h255 kg_3022_2235
    have h257 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2240 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2239 1 h256 kg_3022_2239
    have h258 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2241 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2240 1 h257 kg_3022_2240
    have h259 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2242 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2241 1 h258 kg_3022_2241
    have h260 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2244 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2242 2 h259 kg_3022_2242
    have h261 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2246 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2244 2 h260 kg_3022_2244
    have h262 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2250 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2246 4 h261 kg_3022_2246
    have h263 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2251 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2250 1 h262 kg_3022_2250
    have h264 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2253 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2251 2 h263 kg_3022_2251
    have h265 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2260 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2253 7 h264 kg_3022_2253
    have h266 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2266 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2260 6 h265 kg_3022_2260
    have h267 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2267 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2266 1 h266 kg_3022_2266
    have h268 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2269 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2267 2 h267 kg_3022_2267
    have h269 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2272 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2269 3 h268 kg_3022_2269
    have h270 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2274 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2272 2 h269 kg_3022_2272
    have h271 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2276 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2274 2 h270 kg_3022_2274
    have h272 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2279 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2276 3 h271 kg_3022_2276
    have h273 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2281 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2279 2 h272 kg_3022_2279
    have h274 : IPChk.allR (Pts.glueIB K3022.lits KW_3022) 0 2282 = true := IPChk.allR_join (Pts.glueIB K3022.lits KW_3022) 0 2281 1 h273 kg_3022_2281
    exact h274
  have hlen : K3022.lits.length = 2282 := by decide
  intro k h1 h2
  obtain rfl : k = 3022 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3022) K3022.lits KW_3022
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_530 : ∀ k, 3023 ≤ k → k < 3025 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3023 JW_3023 3023 2 jr_3023
theorem jr6_531 : ∀ k, 3025 ≤ k → k < 3026 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 901 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 6 = true := kb_3025_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 6 3 h0 kb_3025_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 9 10 h1 kb_3025_9
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 19 2 h2 kb_3025_19
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 21 1 h3 kb_3025_21
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 22 12 h4 kb_3025_22
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 34 4 h5 kb_3025_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 38 7 h6 kb_3025_38
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 45 2 h7 kb_3025_45
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 47 29 h8 kb_3025_47
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 76 2 h9 kb_3025_76
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 78 6 h10 kb_3025_78
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 84 2 h11 kb_3025_84
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 86 16 h12 kb_3025_86
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 102 9 h13 kb_3025_102
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 111 7 h14 kb_3025_111
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 118 37 h15 kb_3025_118
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 155 10 h16 kb_3025_155
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 165 16 h17 kb_3025_165
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 181 1 h18 kb_3025_181
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 182 1 h19 kb_3025_182
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 183 1 h20 kb_3025_183
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 184 3 h21 kb_3025_184
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 187 2 h22 kb_3025_187
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 189 29 h23 kb_3025_189
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 218 2 h24 kb_3025_218
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 220 6 h25 kb_3025_220
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 226 2 h26 kb_3025_226
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 228 29 h27 kb_3025_228
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 257 52 h28 kb_3025_257
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 309 6 h29 kb_3025_309
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 315 8 h30 kb_3025_315
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 325 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 323 2 h31 kb_3025_323
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 325 2 h32 kb_3025_325
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 327 44 h33 kb_3025_327
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 371 67 h34 kb_3025_371
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 438 9 h35 kb_3025_438
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 461 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 447 14 h36 kb_3025_447
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 461 13 h37 kb_3025_461
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 474 12 h38 kb_3025_474
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 486 2 h39 kb_3025_486
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 488 6 h40 kb_3025_488
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 494 2 h41 kb_3025_494
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 496 21 h42 kb_3025_496
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 517 2 h43 kb_3025_517
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 519 16 h44 kb_3025_519
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 535 2 h45 kb_3025_535
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 537 12 h46 kb_3025_537
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 549 16 h47 kb_3025_549
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 565 14 h48 kb_3025_565
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 579 1 h49 kb_3025_579
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 580 2 h50 kb_3025_580
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 582 29 h51 kb_3025_582
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 611 2 h52 kb_3025_611
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 621 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 613 8 h53 kb_3025_613
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 621 68 h54 kb_3025_621
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 709 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 689 20 h55 kb_3025_689
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 710 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 709 1 h56 kb_3025_709
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 710 6 h57 kb_3025_710
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 716 3 h58 kb_3025_716
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 719 7 h59 kb_3025_719
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 726 4 h60 kb_3025_726
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 730 10 h61 kb_3025_730
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 764 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 740 24 h62 kb_3025_740
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 764 21 h63 kb_3025_764
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 801 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 785 16 h64 kb_3025_785
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 812 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 801 11 h65 kb_3025_801
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 817 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 812 5 h66 kb_3025_812
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 817 1 h67 kb_3025_817
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 818 8 h68 kb_3025_818
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 839 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 826 13 h69 kb_3025_826
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 839 3 h70 kb_3025_839
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 865 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 842 23 h71 kb_3025_842
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 865 4 h72 kb_3025_865
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 873 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 869 4 h73 kb_3025_869
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 873 2 h74 kb_3025_873
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 887 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 875 12 h75 kb_3025_875
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 897 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 887 10 h76 kb_3025_887
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 901 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 897 4 h77 kb_3025_897
    exact h78
  have hg : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 901 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 6 = true := kg_3025_0
    have h1 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 9 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 6 3 h0 kg_3025_6
    have h2 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 19 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 9 10 h1 kg_3025_9
    have h3 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 21 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 19 2 h2 kg_3025_19
    have h4 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 22 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 21 1 h3 kg_3025_21
    have h5 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 34 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 22 12 h4 kg_3025_22
    have h6 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 38 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 34 4 h5 kg_3025_34
    have h7 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 45 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 38 7 h6 kg_3025_38
    have h8 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 47 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 45 2 h7 kg_3025_45
    have h9 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 76 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 47 29 h8 kg_3025_47
    have h10 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 78 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 76 2 h9 kg_3025_76
    have h11 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 84 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 78 6 h10 kg_3025_78
    have h12 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 86 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 84 2 h11 kg_3025_84
    have h13 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 102 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 86 16 h12 kg_3025_86
    have h14 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 111 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 102 9 h13 kg_3025_102
    have h15 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 118 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 111 7 h14 kg_3025_111
    have h16 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 155 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 118 37 h15 kg_3025_118
    have h17 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 165 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 155 10 h16 kg_3025_155
    have h18 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 181 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 165 16 h17 kg_3025_165
    have h19 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 182 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 181 1 h18 kg_3025_181
    have h20 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 183 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 182 1 h19 kg_3025_182
    have h21 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 184 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 183 1 h20 kg_3025_183
    have h22 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 187 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 184 3 h21 kg_3025_184
    have h23 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 189 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 187 2 h22 kg_3025_187
    have h24 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 218 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 189 29 h23 kg_3025_189
    have h25 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 220 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 218 2 h24 kg_3025_218
    have h26 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 226 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 220 6 h25 kg_3025_220
    have h27 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 228 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 226 2 h26 kg_3025_226
    have h28 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 257 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 228 29 h27 kg_3025_228
    have h29 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 309 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 257 52 h28 kg_3025_257
    have h30 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 315 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 309 6 h29 kg_3025_309
    have h31 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 323 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 315 8 h30 kg_3025_315
    have h32 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 325 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 323 2 h31 kg_3025_323
    have h33 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 327 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 325 2 h32 kg_3025_325
    have h34 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 371 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 327 44 h33 kg_3025_327
    have h35 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 438 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 371 67 h34 kg_3025_371
    have h36 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 447 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 438 9 h35 kg_3025_438
    have h37 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 461 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 447 14 h36 kg_3025_447
    have h38 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 474 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 461 13 h37 kg_3025_461
    have h39 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 486 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 474 12 h38 kg_3025_474
    have h40 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 488 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 486 2 h39 kg_3025_486
    have h41 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 494 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 488 6 h40 kg_3025_488
    have h42 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 496 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 494 2 h41 kg_3025_494
    have h43 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 517 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 496 21 h42 kg_3025_496
    have h44 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 519 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 517 2 h43 kg_3025_517
    have h45 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 535 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 519 16 h44 kg_3025_519
    have h46 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 537 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 535 2 h45 kg_3025_535
    have h47 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 549 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 537 12 h46 kg_3025_537
    have h48 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 565 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 549 16 h47 kg_3025_549
    have h49 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 579 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 565 14 h48 kg_3025_565
    have h50 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 580 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 579 1 h49 kg_3025_579
    have h51 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 582 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 580 2 h50 kg_3025_580
    have h52 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 611 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 582 29 h51 kg_3025_582
    have h53 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 613 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 611 2 h52 kg_3025_611
    have h54 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 621 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 613 8 h53 kg_3025_613
    have h55 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 689 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 621 68 h54 kg_3025_621
    have h56 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 709 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 689 20 h55 kg_3025_689
    have h57 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 710 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 709 1 h56 kg_3025_709
    have h58 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 716 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 710 6 h57 kg_3025_710
    have h59 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 719 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 716 3 h58 kg_3025_716
    have h60 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 726 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 719 7 h59 kg_3025_719
    have h61 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 730 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 726 4 h60 kg_3025_726
    have h62 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 740 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 730 10 h61 kg_3025_730
    have h63 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 764 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 740 24 h62 kg_3025_740
    have h64 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 785 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 764 21 h63 kg_3025_764
    have h65 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 801 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 785 16 h64 kg_3025_785
    have h66 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 812 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 801 11 h65 kg_3025_801
    have h67 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 817 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 812 5 h66 kg_3025_812
    have h68 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 818 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 817 1 h67 kg_3025_817
    have h69 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 826 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 818 8 h68 kg_3025_818
    have h70 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 839 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 826 13 h69 kg_3025_826
    have h71 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 842 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 839 3 h70 kg_3025_839
    have h72 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 865 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 842 23 h71 kg_3025_842
    have h73 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 869 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 865 4 h72 kg_3025_865
    have h74 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 873 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 869 4 h73 kg_3025_869
    have h75 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 875 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 873 2 h74 kg_3025_873
    have h76 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 887 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 875 12 h75 kg_3025_875
    have h77 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 897 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 887 10 h76 kg_3025_887
    have h78 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 901 = true := IPChk.allR_join (Pts.glueIB K3025.lits KW_3025) 0 897 4 h77 kg_3025_897
    exact h78
  have hlen : K3025.lits.length = 901 := by decide
  intro k h1 h2
  obtain rfl : k = 3025 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3025) K3025.lits KW_3025
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_532 : ∀ k, 3026 ≤ k → k < 3027 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 219 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 1 = true := kb_3026_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 1 6 h0 kb_3026_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 7 1 h1 kb_3026_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 8 1 h2 kb_3026_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 9 18 h3 kb_3026_9
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 27 11 h4 kb_3026_27
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 38 5 h5 kb_3026_38
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 43 6 h6 kb_3026_43
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 49 23 h7 kb_3026_49
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 72 25 h8 kb_3026_72
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 97 40 h9 kb_3026_97
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 137 4 h10 kb_3026_137
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 141 23 h11 kb_3026_141
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3026.lits.getD i 0)) 0 164 55 h12 kb_3026_164
    exact h13
  have hg : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 219 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 1 = true := kg_3026_0
    have h1 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 7 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 1 6 h0 kg_3026_1
    have h2 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 8 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 7 1 h1 kg_3026_7
    have h3 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 9 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 8 1 h2 kg_3026_8
    have h4 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 27 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 9 18 h3 kg_3026_9
    have h5 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 38 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 27 11 h4 kg_3026_27
    have h6 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 43 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 38 5 h5 kg_3026_38
    have h7 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 49 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 43 6 h6 kg_3026_43
    have h8 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 72 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 49 23 h7 kg_3026_49
    have h9 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 97 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 72 25 h8 kg_3026_72
    have h10 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 137 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 97 40 h9 kg_3026_97
    have h11 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 141 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 137 4 h10 kg_3026_137
    have h12 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 164 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 141 23 h11 kg_3026_141
    have h13 : IPChk.allR (Pts.glueIB K3026.lits KW_3026) 0 219 = true := IPChk.allR_join (Pts.glueIB K3026.lits KW_3026) 0 164 55 h12 kg_3026_164
    exact h13
  have hlen : K3026.lits.length = 219 := by decide
  intro k h1 h2
  obtain rfl : k = 3026 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3026) K3026.lits KW_3026
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_533 : ∀ k, 3027 ≤ k → k < 3029 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3027 JW_3027 3027 2 jr_3027
theorem jr6_534 : ∀ k, 3029 ≤ k → k < 3030 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 537 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 3 = true := kb_3029_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 3 8 h0 kb_3029_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 11 8 h1 kb_3029_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 19 1 h2 kb_3029_19
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 20 10 h3 kb_3029_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 30 11 h4 kb_3029_30
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 41 43 h5 kb_3029_41
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 84 6 h6 kb_3029_84
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 90 15 h7 kb_3029_90
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 105 2 h8 kb_3029_105
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 107 43 h9 kb_3029_107
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 150 79 h10 kb_3029_150
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 229 9 h11 kb_3029_229
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 238 4 h12 kb_3029_238
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 242 26 h13 kb_3029_242
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 268 43 h14 kb_3029_268
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 311 1 h15 kb_3029_311
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 312 4 h16 kb_3029_312
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 316 31 h17 kb_3029_316
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 386 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 347 39 h18 kb_3029_347
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 386 20 h19 kb_3029_386
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 406 94 h20 kb_3029_406
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 500 35 h21 kb_3029_500
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3029.lits.getD i 0)) 0 535 2 h22 kb_3029_535
    exact h23
  have hg : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 537 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 3 = true := kg_3029_0
    have h1 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 11 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 3 8 h0 kg_3029_3
    have h2 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 19 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 11 8 h1 kg_3029_11
    have h3 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 20 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 19 1 h2 kg_3029_19
    have h4 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 30 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 20 10 h3 kg_3029_20
    have h5 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 41 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 30 11 h4 kg_3029_30
    have h6 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 84 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 41 43 h5 kg_3029_41
    have h7 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 90 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 84 6 h6 kg_3029_84
    have h8 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 105 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 90 15 h7 kg_3029_90
    have h9 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 107 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 105 2 h8 kg_3029_105
    have h10 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 150 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 107 43 h9 kg_3029_107
    have h11 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 229 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 150 79 h10 kg_3029_150
    have h12 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 238 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 229 9 h11 kg_3029_229
    have h13 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 242 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 238 4 h12 kg_3029_238
    have h14 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 268 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 242 26 h13 kg_3029_242
    have h15 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 311 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 268 43 h14 kg_3029_268
    have h16 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 312 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 311 1 h15 kg_3029_311
    have h17 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 316 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 312 4 h16 kg_3029_312
    have h18 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 347 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 316 31 h17 kg_3029_316
    have h19 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 386 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 347 39 h18 kg_3029_347
    have h20 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 406 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 386 20 h19 kg_3029_386
    have h21 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 500 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 406 94 h20 kg_3029_406
    have h22 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 535 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 500 35 h21 kg_3029_500
    have h23 : IPChk.allR (Pts.glueIB K3029.lits KW_3029) 0 537 = true := IPChk.allR_join (Pts.glueIB K3029.lits KW_3029) 0 535 2 h22 kg_3029_535
    exact h23
  have hlen : K3029.lits.length = 537 := by decide
  intro k h1 h2
  obtain rfl : k = 3029 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3029) K3029.lits KW_3029
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_535 : ∀ k, 3030 ≤ k → k < 3031 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 276 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 2 = true := kb_3030_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 2 8 h0 kb_3030_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 10 8 h1 kb_3030_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 18 1 h2 kb_3030_18
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 19 11 h3 kb_3030_19
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 30 43 h4 kb_3030_30
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 73 8 h5 kb_3030_73
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 81 16 h6 kb_3030_81
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 97 1 h7 kb_3030_97
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 98 9 h8 kb_3030_98
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 107 26 h9 kb_3030_107
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 133 48 h10 kb_3030_133
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 181 17 h11 kb_3030_181
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 198 31 h12 kb_3030_198
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 229 2 h13 kb_3030_229
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 231 5 h14 kb_3030_231
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 0 236 40 h15 kb_3030_236
    exact h16
  have hg : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 276 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 2 = true := kg_3030_0
    have h1 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 10 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 2 8 h0 kg_3030_2
    have h2 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 18 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 10 8 h1 kg_3030_10
    have h3 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 19 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 18 1 h2 kg_3030_18
    have h4 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 30 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 19 11 h3 kg_3030_19
    have h5 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 73 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 30 43 h4 kg_3030_30
    have h6 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 81 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 73 8 h5 kg_3030_73
    have h7 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 97 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 81 16 h6 kg_3030_81
    have h8 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 98 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 97 1 h7 kg_3030_97
    have h9 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 107 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 98 9 h8 kg_3030_98
    have h10 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 133 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 107 26 h9 kg_3030_107
    have h11 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 181 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 133 48 h10 kg_3030_133
    have h12 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 198 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 181 17 h11 kg_3030_181
    have h13 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 229 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 198 31 h12 kg_3030_198
    have h14 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 231 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 229 2 h13 kg_3030_229
    have h15 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 236 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 231 5 h14 kg_3030_231
    have h16 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 0 276 = true := IPChk.allR_join (Pts.glueIB K3030.lits KW_3030) 0 236 40 h15 kg_3030_236
    exact h16
  have hlen : K3030.lits.length = 276 := by decide
  intro k h1 h2
  obtain rfl : k = 3030 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3030) K3030.lits KW_3030
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_536 : ∀ k, 3031 ≤ k → k < 3032 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3031 JW_3031 3031 1 jr_3031
theorem jr6_537 : ∀ k, 3032 ≤ k → k < 3033 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 689 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 1 = true := kb_3032_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 1 1 h0 kb_3032_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 2 1 h1 kb_3032_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 3 14 h2 kb_3032_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 17 17 h3 kb_3032_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 34 6 h4 kb_3032_34
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 40 2 h5 kb_3032_40
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 42 19 h6 kb_3032_42
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 61 3 h7 kb_3032_61
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 64 2 h8 kb_3032_64
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 66 5 h9 kb_3032_66
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 71 11 h10 kb_3032_71
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 82 25 h11 kb_3032_82
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 107 2 h12 kb_3032_107
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 109 25 h13 kb_3032_109
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 134 5 h14 kb_3032_134
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 139 15 h15 kb_3032_139
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 154 6 h16 kb_3032_154
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 160 2 h17 kb_3032_160
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 162 20 h18 kb_3032_162
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 182 8 h19 kb_3032_182
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 190 20 h20 kb_3032_190
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 210 2 h21 kb_3032_210
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 212 17 h22 kb_3032_212
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 229 1 h23 kb_3032_229
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 230 20 h24 kb_3032_230
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 250 1 h25 kb_3032_250
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 251 1 h26 kb_3032_251
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 252 19 h27 kb_3032_252
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 271 85 h28 kb_3032_271
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 356 4 h29 kb_3032_356
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 360 3 h30 kb_3032_360
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 363 61 h31 kb_3032_363
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 424 23 h32 kb_3032_424
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 447 17 h33 kb_3032_447
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 464 33 h34 kb_3032_464
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 497 2 h35 kb_3032_497
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 499 19 h36 kb_3032_499
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 518 28 h37 kb_3032_518
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 546 3 h38 kb_3032_546
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 549 29 h39 kb_3032_549
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 628 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 578 50 h40 kb_3032_578
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 628 8 h41 kb_3032_628
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 636 32 h42 kb_3032_636
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3032.lits.getD i 0)) 0 668 21 h43 kb_3032_668
    exact h44
  have hg : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 689 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 1 = true := kg_3032_0
    have h1 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 2 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 1 1 h0 kg_3032_1
    have h2 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 3 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 2 1 h1 kg_3032_2
    have h3 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 17 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 3 14 h2 kg_3032_3
    have h4 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 34 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 17 17 h3 kg_3032_17
    have h5 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 40 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 34 6 h4 kg_3032_34
    have h6 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 42 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 40 2 h5 kg_3032_40
    have h7 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 61 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 42 19 h6 kg_3032_42
    have h8 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 64 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 61 3 h7 kg_3032_61
    have h9 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 66 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 64 2 h8 kg_3032_64
    have h10 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 71 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 66 5 h9 kg_3032_66
    have h11 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 82 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 71 11 h10 kg_3032_71
    have h12 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 107 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 82 25 h11 kg_3032_82
    have h13 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 109 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 107 2 h12 kg_3032_107
    have h14 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 134 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 109 25 h13 kg_3032_109
    have h15 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 139 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 134 5 h14 kg_3032_134
    have h16 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 154 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 139 15 h15 kg_3032_139
    have h17 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 160 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 154 6 h16 kg_3032_154
    have h18 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 162 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 160 2 h17 kg_3032_160
    have h19 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 182 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 162 20 h18 kg_3032_162
    have h20 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 190 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 182 8 h19 kg_3032_182
    have h21 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 210 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 190 20 h20 kg_3032_190
    have h22 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 212 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 210 2 h21 kg_3032_210
    have h23 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 229 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 212 17 h22 kg_3032_212
    have h24 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 230 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 229 1 h23 kg_3032_229
    have h25 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 250 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 230 20 h24 kg_3032_230
    have h26 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 251 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 250 1 h25 kg_3032_250
    have h27 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 252 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 251 1 h26 kg_3032_251
    have h28 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 271 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 252 19 h27 kg_3032_252
    have h29 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 356 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 271 85 h28 kg_3032_271
    have h30 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 360 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 356 4 h29 kg_3032_356
    have h31 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 363 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 360 3 h30 kg_3032_360
    have h32 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 424 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 363 61 h31 kg_3032_363
    have h33 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 447 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 424 23 h32 kg_3032_424
    have h34 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 464 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 447 17 h33 kg_3032_447
    have h35 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 497 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 464 33 h34 kg_3032_464
    have h36 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 499 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 497 2 h35 kg_3032_497
    have h37 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 518 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 499 19 h36 kg_3032_499
    have h38 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 546 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 518 28 h37 kg_3032_518
    have h39 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 549 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 546 3 h38 kg_3032_546
    have h40 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 578 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 549 29 h39 kg_3032_549
    have h41 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 628 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 578 50 h40 kg_3032_578
    have h42 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 636 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 628 8 h41 kg_3032_628
    have h43 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 668 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 636 32 h42 kg_3032_636
    have h44 : IPChk.allR (Pts.glueIB K3032.lits KW_3032) 0 689 = true := IPChk.allR_join (Pts.glueIB K3032.lits KW_3032) 0 668 21 h43 kg_3032_668
    exact h44
  have hlen : K3032.lits.length = 689 := by decide
  intro k h1 h2
  obtain rfl : k = 3032 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3032) K3032.lits KW_3032
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_538 : ∀ k, 3033 ≤ k → k < 3040 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3033 JW_3033 3033 7 jr_3033
theorem jr6_539 : ∀ k, 3040 ≤ k → k < 3041 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 73 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 2 = true := kb_3040_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 2 6 h0 kb_3040_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 8 22 h1 kb_3040_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 30 4 h2 kb_3040_30
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 34 22 h3 kb_3040_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 56 17 h4 kb_3040_56
    exact h5
  have hg : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 73 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 2 = true := kg_3040_0
    have h1 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 8 = true := IPChk.allR_join (Pts.glueIB K3040.lits KW_3040) 0 2 6 h0 kg_3040_2
    have h2 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 30 = true := IPChk.allR_join (Pts.glueIB K3040.lits KW_3040) 0 8 22 h1 kg_3040_8
    have h3 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 34 = true := IPChk.allR_join (Pts.glueIB K3040.lits KW_3040) 0 30 4 h2 kg_3040_30
    have h4 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 56 = true := IPChk.allR_join (Pts.glueIB K3040.lits KW_3040) 0 34 22 h3 kg_3040_34
    have h5 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 73 = true := IPChk.allR_join (Pts.glueIB K3040.lits KW_3040) 0 56 17 h4 kg_3040_56
    exact h5
  have hlen : K3040.lits.length = 73 := by decide
  intro k h1 h2
  obtain rfl : k = 3040 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3040) K3040.lits KW_3040
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_540 : ∀ k, 3041 ≤ k → k < 3048 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3041 JW_3041 3041 7 jr_3041
theorem jr6_541 : ∀ k, 3048 ≤ k → k < 3049 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 0 4 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 0 1 = true := kb_3048_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3048.lits.getD i 0)) 0 1 3 h0 kb_3048_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K3048.lits KW_3048) 0 4 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3048.lits KW_3048) 0 1 = true := kg_3048_0
    have h1 : IPChk.allR (Pts.glueIB K3048.lits KW_3048) 0 4 = true := IPChk.allR_join (Pts.glueIB K3048.lits KW_3048) 0 1 3 h0 kg_3048_1
    exact h1
  have hlen : K3048.lits.length = 4 := by decide
  intro k h1 h2
  obtain rfl : k = 3048 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3048) K3048.lits KW_3048
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_542 : ∀ k, 3049 ≤ k → k < 3077 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3049 JW_3049 3049 28 jr_3049
theorem jr6_543 : ∀ k, 3077 ≤ k → k < 3078 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1438 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 3 = true := kb_3077_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 3 5 h0 kb_3077_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 8 13 h1 kb_3077_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 21 7 h2 kb_3077_21
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 28 11 h3 kb_3077_28
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 39 5 h4 kb_3077_39
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 44 8 h5 kb_3077_44
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 52 1 h6 kb_3077_52
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 53 1 h7 kb_3077_53
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 54 21 h8 kb_3077_54
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 75 2 h9 kb_3077_75
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 77 6 h10 kb_3077_77
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 83 2 h11 kb_3077_83
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 85 20 h12 kb_3077_85
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 105 2 h13 kb_3077_105
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 107 3 h14 kb_3077_107
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 110 8 h15 kb_3077_110
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 118 20 h16 kb_3077_118
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 138 1 h17 kb_3077_138
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 139 2 h18 kb_3077_139
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 141 6 h19 kb_3077_141
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 147 1 h20 kb_3077_147
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 148 1 h21 kb_3077_148
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 149 19 h22 kb_3077_149
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 168 2 h23 kb_3077_168
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 170 6 h24 kb_3077_170
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 176 2 h25 kb_3077_176
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 178 21 h26 kb_3077_178
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 199 8 h27 kb_3077_199
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 207 16 h28 kb_3077_207
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 223 4 h29 kb_3077_223
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 227 1 h30 kb_3077_227
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 228 15 h31 kb_3077_228
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 243 2 h32 kb_3077_243
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 245 6 h33 kb_3077_245
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 251 2 h34 kb_3077_251
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 266 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 253 13 h35 kb_3077_253
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 266 11 h36 kb_3077_266
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 277 12 h37 kb_3077_277
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 293 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 289 4 h38 kb_3077_289
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 314 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 293 21 h39 kb_3077_293
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 314 2 h40 kb_3077_314
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 316 23 h41 kb_3077_316
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 339 2 h42 kb_3077_339
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 341 14 h43 kb_3077_341
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 355 3 h44 kb_3077_355
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 358 7 h45 kb_3077_358
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 365 20 h46 kb_3077_365
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 385 7 h47 kb_3077_385
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 394 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 392 2 h48 kb_3077_392
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 394 20 h49 kb_3077_394
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 414 2 h50 kb_3077_414
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 416 17 h51 kb_3077_416
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 435 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 433 2 h52 kb_3077_433
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 435 17 h53 kb_3077_435
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 452 3 h54 kb_3077_452
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 478 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 455 23 h55 kb_3077_455
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 478 1 h56 kb_3077_478
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 479 2 h57 kb_3077_479
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 481 3 h58 kb_3077_481
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 484 1 h59 kb_3077_484
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 485 1 h60 kb_3077_485
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 486 2 h61 kb_3077_486
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 488 1 h62 kb_3077_488
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 490 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 489 1 h63 kb_3077_489
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 490 6 h64 kb_3077_490
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 496 15 h65 kb_3077_496
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 511 27 h66 kb_3077_511
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 538 2 h67 kb_3077_538
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 540 13 h68 kb_3077_540
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 553 6 h69 kb_3077_553
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 559 1 h70 kb_3077_559
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 560 18 h71 kb_3077_560
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 578 2 h72 kb_3077_578
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 580 11 h73 kb_3077_580
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 591 31 h74 kb_3077_591
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 625 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 622 3 h75 kb_3077_622
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 625 1 h76 kb_3077_625
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 628 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 626 2 h77 kb_3077_626
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 628 12 h78 kb_3077_628
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 640 18 h79 kb_3077_640
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 658 2 h80 kb_3077_658
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 671 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 660 11 h81 kb_3077_660
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 671 5 h82 kb_3077_671
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 676 1 h83 kb_3077_676
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 677 9 h84 kb_3077_677
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 686 1 h85 kb_3077_686
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 687 5 h86 kb_3077_687
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 692 14 h87 kb_3077_692
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 709 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 706 3 h88 kb_3077_706
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 709 10 h89 kb_3077_709
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 721 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 719 2 h90 kb_3077_719
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 727 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 721 6 h91 kb_3077_721
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 727 15 h92 kb_3077_727
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 744 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 742 2 h93 kb_3077_742
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 746 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 744 2 h94 kb_3077_744
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 746 24 h95 kb_3077_746
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 770 19 h96 kb_3077_770
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 789 29 h97 kb_3077_789
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 818 8 h98 kb_3077_818
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 826 29 h99 kb_3077_826
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 855 7 h100 kb_3077_855
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 864 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 862 2 h101 kb_3077_862
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 879 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 864 15 h102 kb_3077_864
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 901 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 879 22 h103 kb_3077_879
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 901 2 h104 kb_3077_901
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 912 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 903 9 h105 kb_3077_903
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 918 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 912 6 h106 kb_3077_912
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 946 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 918 28 h107 kb_3077_918
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 947 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 946 1 h108 kb_3077_946
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 950 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 947 3 h109 kb_3077_947
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 953 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 950 3 h110 kb_3077_950
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 953 1 h111 kb_3077_953
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 954 1 h112 kb_3077_954
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 956 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 955 1 h113 kb_3077_955
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 981 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 956 25 h114 kb_3077_956
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 988 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 981 7 h115 kb_3077_981
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 988 6 h116 kb_3077_988
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1003 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 994 9 h117 kb_3077_994
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1003 69 h118 kb_3077_1003
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1074 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1072 2 h119 kb_3077_1072
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1075 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1074 1 h120 kb_3077_1074
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1092 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1075 17 h121 kb_3077_1075
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1092 5 h122 kb_3077_1092
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1097 7 h123 kb_3077_1097
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1104 9 h124 kb_3077_1104
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1113 46 h125 kb_3077_1113
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1159 2 h126 kb_3077_1159
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1161 6 h127 kb_3077_1161
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1167 9 h128 kb_3077_1167
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1176 69 h129 kb_3077_1176
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1245 1 h130 kb_3077_1245
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1246 1 h131 kb_3077_1246
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1247 11 h132 kb_3077_1247
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1258 2 h133 kb_3077_1258
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1260 4 h134 kb_3077_1260
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1264 6 h135 kb_3077_1264
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1270 3 h136 kb_3077_1270
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1273 1 h137 kb_3077_1273
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1274 5 h138 kb_3077_1274
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1279 4 h139 kb_3077_1279
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1283 19 h140 kb_3077_1283
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1302 33 h141 kb_3077_1302
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1335 27 h142 kb_3077_1335
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1362 20 h143 kb_3077_1362
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1397 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1382 15 h144 kb_3077_1382
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1397 1 h145 kb_3077_1397
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1398 1 h146 kb_3077_1398
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1399 2 h147 kb_3077_1399
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1401 2 h148 kb_3077_1401
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1403 1 h149 kb_3077_1403
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1404 3 h150 kb_3077_1404
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1407 11 h151 kb_3077_1407
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1418 4 h152 kb_3077_1418
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1422 2 h153 kb_3077_1422
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1424 7 h154 kb_3077_1424
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3077.lits.getD i 0)) 0 1431 7 h155 kb_3077_1431
    exact h156
  have hg : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1438 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 3 = true := kg_3077_0
    have h1 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 8 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 3 5 h0 kg_3077_3
    have h2 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 21 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 8 13 h1 kg_3077_8
    have h3 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 28 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 21 7 h2 kg_3077_21
    have h4 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 39 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 28 11 h3 kg_3077_28
    have h5 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 44 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 39 5 h4 kg_3077_39
    have h6 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 52 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 44 8 h5 kg_3077_44
    have h7 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 53 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 52 1 h6 kg_3077_52
    have h8 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 54 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 53 1 h7 kg_3077_53
    have h9 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 75 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 54 21 h8 kg_3077_54
    have h10 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 77 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 75 2 h9 kg_3077_75
    have h11 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 83 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 77 6 h10 kg_3077_77
    have h12 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 85 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 83 2 h11 kg_3077_83
    have h13 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 105 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 85 20 h12 kg_3077_85
    have h14 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 107 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 105 2 h13 kg_3077_105
    have h15 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 110 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 107 3 h14 kg_3077_107
    have h16 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 118 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 110 8 h15 kg_3077_110
    have h17 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 138 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 118 20 h16 kg_3077_118
    have h18 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 139 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 138 1 h17 kg_3077_138
    have h19 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 141 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 139 2 h18 kg_3077_139
    have h20 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 147 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 141 6 h19 kg_3077_141
    have h21 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 148 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 147 1 h20 kg_3077_147
    have h22 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 149 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 148 1 h21 kg_3077_148
    have h23 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 168 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 149 19 h22 kg_3077_149
    have h24 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 170 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 168 2 h23 kg_3077_168
    have h25 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 176 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 170 6 h24 kg_3077_170
    have h26 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 178 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 176 2 h25 kg_3077_176
    have h27 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 199 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 178 21 h26 kg_3077_178
    have h28 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 207 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 199 8 h27 kg_3077_199
    have h29 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 223 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 207 16 h28 kg_3077_207
    have h30 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 227 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 223 4 h29 kg_3077_223
    have h31 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 228 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 227 1 h30 kg_3077_227
    have h32 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 243 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 228 15 h31 kg_3077_228
    have h33 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 245 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 243 2 h32 kg_3077_243
    have h34 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 251 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 245 6 h33 kg_3077_245
    have h35 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 253 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 251 2 h34 kg_3077_251
    have h36 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 266 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 253 13 h35 kg_3077_253
    have h37 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 277 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 266 11 h36 kg_3077_266
    have h38 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 289 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 277 12 h37 kg_3077_277
    have h39 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 293 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 289 4 h38 kg_3077_289
    have h40 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 314 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 293 21 h39 kg_3077_293
    have h41 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 316 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 314 2 h40 kg_3077_314
    have h42 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 339 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 316 23 h41 kg_3077_316
    have h43 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 341 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 339 2 h42 kg_3077_339
    have h44 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 355 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 341 14 h43 kg_3077_341
    have h45 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 358 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 355 3 h44 kg_3077_355
    have h46 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 365 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 358 7 h45 kg_3077_358
    have h47 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 385 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 365 20 h46 kg_3077_365
    have h48 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 392 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 385 7 h47 kg_3077_385
    have h49 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 394 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 392 2 h48 kg_3077_392
    have h50 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 414 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 394 20 h49 kg_3077_394
    have h51 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 416 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 414 2 h50 kg_3077_414
    have h52 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 433 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 416 17 h51 kg_3077_416
    have h53 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 435 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 433 2 h52 kg_3077_433
    have h54 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 452 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 435 17 h53 kg_3077_435
    have h55 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 455 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 452 3 h54 kg_3077_452
    have h56 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 478 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 455 23 h55 kg_3077_455
    have h57 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 479 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 478 1 h56 kg_3077_478
    have h58 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 481 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 479 2 h57 kg_3077_479
    have h59 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 484 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 481 3 h58 kg_3077_481
    have h60 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 485 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 484 1 h59 kg_3077_484
    have h61 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 486 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 485 1 h60 kg_3077_485
    have h62 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 488 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 486 2 h61 kg_3077_486
    have h63 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 489 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 488 1 h62 kg_3077_488
    have h64 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 490 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 489 1 h63 kg_3077_489
    have h65 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 496 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 490 6 h64 kg_3077_490
    have h66 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 511 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 496 15 h65 kg_3077_496
    have h67 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 538 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 511 27 h66 kg_3077_511
    have h68 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 540 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 538 2 h67 kg_3077_538
    have h69 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 553 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 540 13 h68 kg_3077_540
    have h70 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 559 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 553 6 h69 kg_3077_553
    have h71 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 560 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 559 1 h70 kg_3077_559
    have h72 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 578 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 560 18 h71 kg_3077_560
    have h73 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 580 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 578 2 h72 kg_3077_578
    have h74 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 591 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 580 11 h73 kg_3077_580
    have h75 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 622 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 591 31 h74 kg_3077_591
    have h76 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 625 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 622 3 h75 kg_3077_622
    have h77 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 626 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 625 1 h76 kg_3077_625
    have h78 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 628 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 626 2 h77 kg_3077_626
    have h79 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 640 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 628 12 h78 kg_3077_628
    have h80 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 658 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 640 18 h79 kg_3077_640
    have h81 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 660 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 658 2 h80 kg_3077_658
    have h82 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 671 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 660 11 h81 kg_3077_660
    have h83 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 676 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 671 5 h82 kg_3077_671
    have h84 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 677 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 676 1 h83 kg_3077_676
    have h85 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 686 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 677 9 h84 kg_3077_677
    have h86 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 687 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 686 1 h85 kg_3077_686
    have h87 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 692 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 687 5 h86 kg_3077_687
    have h88 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 706 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 692 14 h87 kg_3077_692
    have h89 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 709 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 706 3 h88 kg_3077_706
    have h90 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 719 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 709 10 h89 kg_3077_709
    have h91 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 721 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 719 2 h90 kg_3077_719
    have h92 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 727 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 721 6 h91 kg_3077_721
    have h93 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 742 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 727 15 h92 kg_3077_727
    have h94 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 744 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 742 2 h93 kg_3077_742
    have h95 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 746 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 744 2 h94 kg_3077_744
    have h96 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 770 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 746 24 h95 kg_3077_746
    have h97 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 789 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 770 19 h96 kg_3077_770
    have h98 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 818 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 789 29 h97 kg_3077_789
    have h99 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 826 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 818 8 h98 kg_3077_818
    have h100 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 855 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 826 29 h99 kg_3077_826
    have h101 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 862 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 855 7 h100 kg_3077_855
    have h102 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 864 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 862 2 h101 kg_3077_862
    have h103 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 879 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 864 15 h102 kg_3077_864
    have h104 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 901 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 879 22 h103 kg_3077_879
    have h105 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 903 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 901 2 h104 kg_3077_901
    have h106 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 912 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 903 9 h105 kg_3077_903
    have h107 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 918 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 912 6 h106 kg_3077_912
    have h108 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 946 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 918 28 h107 kg_3077_918
    have h109 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 947 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 946 1 h108 kg_3077_946
    have h110 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 950 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 947 3 h109 kg_3077_947
    have h111 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 953 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 950 3 h110 kg_3077_950
    have h112 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 954 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 953 1 h111 kg_3077_953
    have h113 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 955 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 954 1 h112 kg_3077_954
    have h114 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 956 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 955 1 h113 kg_3077_955
    have h115 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 981 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 956 25 h114 kg_3077_956
    have h116 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 988 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 981 7 h115 kg_3077_981
    have h117 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 994 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 988 6 h116 kg_3077_988
    have h118 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1003 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 994 9 h117 kg_3077_994
    have h119 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1072 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1003 69 h118 kg_3077_1003
    have h120 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1074 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1072 2 h119 kg_3077_1072
    have h121 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1075 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1074 1 h120 kg_3077_1074
    have h122 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1092 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1075 17 h121 kg_3077_1075
    have h123 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1097 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1092 5 h122 kg_3077_1092
    have h124 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1104 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1097 7 h123 kg_3077_1097
    have h125 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1113 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1104 9 h124 kg_3077_1104
    have h126 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1159 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1113 46 h125 kg_3077_1113
    have h127 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1161 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1159 2 h126 kg_3077_1159
    have h128 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1167 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1161 6 h127 kg_3077_1161
    have h129 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1176 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1167 9 h128 kg_3077_1167
    have h130 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1245 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1176 69 h129 kg_3077_1176
    have h131 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1246 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1245 1 h130 kg_3077_1245
    have h132 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1247 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1246 1 h131 kg_3077_1246
    have h133 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1258 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1247 11 h132 kg_3077_1247
    have h134 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1260 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1258 2 h133 kg_3077_1258
    have h135 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1264 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1260 4 h134 kg_3077_1260
    have h136 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1270 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1264 6 h135 kg_3077_1264
    have h137 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1273 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1270 3 h136 kg_3077_1270
    have h138 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1274 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1273 1 h137 kg_3077_1273
    have h139 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1279 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1274 5 h138 kg_3077_1274
    have h140 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1283 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1279 4 h139 kg_3077_1279
    have h141 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1302 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1283 19 h140 kg_3077_1283
    have h142 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1335 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1302 33 h141 kg_3077_1302
    have h143 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1362 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1335 27 h142 kg_3077_1335
    have h144 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1382 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1362 20 h143 kg_3077_1362
    have h145 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1397 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1382 15 h144 kg_3077_1382
    have h146 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1398 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1397 1 h145 kg_3077_1397
    have h147 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1399 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1398 1 h146 kg_3077_1398
    have h148 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1401 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1399 2 h147 kg_3077_1399
    have h149 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1403 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1401 2 h148 kg_3077_1401
    have h150 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1404 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1403 1 h149 kg_3077_1403
    have h151 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1407 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1404 3 h150 kg_3077_1404
    have h152 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1418 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1407 11 h151 kg_3077_1407
    have h153 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1422 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1418 4 h152 kg_3077_1418
    have h154 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1424 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1422 2 h153 kg_3077_1422
    have h155 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1431 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1424 7 h154 kg_3077_1424
    have h156 : IPChk.allR (Pts.glueIB K3077.lits KW_3077) 0 1438 = true := IPChk.allR_join (Pts.glueIB K3077.lits KW_3077) 0 1431 7 h155 kg_3077_1431
    exact h156
  have hlen : K3077.lits.length = 1438 := by decide
  intro k h1 h2
  obtain rfl : k = 3077 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3077) K3077.lits KW_3077
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_544 : ∀ k, 3078 ≤ k → k < 3079 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_3078 JW_3078 3078 1 jr_3078
theorem jr6_545 : ∀ k, 3079 ≤ k → k < 3080 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 348 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 1 = true := kb_3079_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 1 6 h0 kb_3079_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 7 6 h1 kb_3079_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 13 1 h2 kb_3079_13
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 14 16 h3 kb_3079_14
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 30 4 h4 kb_3079_30
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 34 4 h5 kb_3079_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 38 21 h6 kb_3079_38
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 59 28 h7 kb_3079_59
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 87 21 h8 kb_3079_87
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 108 32 h9 kb_3079_108
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 140 2 h10 kb_3079_140
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 142 11 h11 kb_3079_142
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 153 4 h12 kb_3079_153
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 157 5 h13 kb_3079_157
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 162 55 h14 kb_3079_162
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 217 23 h15 kb_3079_217
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 240 17 h16 kb_3079_240
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 257 7 h17 kb_3079_257
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 264 37 h18 kb_3079_264
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 301 37 h19 kb_3079_301
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3079.lits.getD i 0)) 0 338 10 h20 kb_3079_338
    exact h21
  have hg : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 348 = true := by
    have h0 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 1 = true := kg_3079_0
    have h1 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 7 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 1 6 h0 kg_3079_1
    have h2 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 13 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 7 6 h1 kg_3079_7
    have h3 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 14 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 13 1 h2 kg_3079_13
    have h4 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 30 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 14 16 h3 kg_3079_14
    have h5 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 34 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 30 4 h4 kg_3079_30
    have h6 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 38 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 34 4 h5 kg_3079_34
    have h7 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 59 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 38 21 h6 kg_3079_38
    have h8 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 87 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 59 28 h7 kg_3079_59
    have h9 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 108 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 87 21 h8 kg_3079_87
    have h10 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 140 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 108 32 h9 kg_3079_108
    have h11 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 142 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 140 2 h10 kg_3079_140
    have h12 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 153 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 142 11 h11 kg_3079_142
    have h13 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 157 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 153 4 h12 kg_3079_153
    have h14 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 162 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 157 5 h13 kg_3079_157
    have h15 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 217 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 162 55 h14 kg_3079_162
    have h16 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 240 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 217 23 h15 kg_3079_217
    have h17 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 257 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 240 17 h16 kg_3079_240
    have h18 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 264 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 257 7 h17 kg_3079_257
    have h19 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 301 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 264 37 h18 kg_3079_264
    have h20 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 338 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 301 37 h19 kg_3079_301
    have h21 : IPChk.allR (Pts.glueIB K3079.lits KW_3079) 0 348 = true := IPChk.allR_join (Pts.glueIB K3079.lits KW_3079) 0 338 10 h20 kg_3079_338
    exact h21
  have hlen : K3079.lits.length = 348 := by decide
  intro k h1 h2
  obtain rfl : k = 3079 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 3079) K3079.lits KW_3079
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)

theorem grp6_18 : ∀ k, 3022 ≤ k → k < 3080 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_529
  have a1 := Pts.fa_join a0 jr6_530
  have a2 := Pts.fa_join a1 jr6_531
  have a3 := Pts.fa_join a2 jr6_532
  have a4 := Pts.fa_join a3 jr6_533
  have a5 := Pts.fa_join a4 jr6_534
  have a6 := Pts.fa_join a5 jr6_535
  have a7 := Pts.fa_join a6 jr6_536
  have a8 := Pts.fa_join a7 jr6_537
  have a9 := Pts.fa_join a8 jr6_538
  have a10 := Pts.fa_join a9 jr6_539
  have a11 := Pts.fa_join a10 jr6_540
  have a12 := Pts.fa_join a11 jr6_541
  have a13 := Pts.fa_join a12 jr6_542
  have a14 := Pts.fa_join a13 jr6_543
  have a15 := Pts.fa_join a14 jr6_544
  have a16 := Pts.fa_join a15 jr6_545
  exact a16

end B334.E1x.Pts.S707
