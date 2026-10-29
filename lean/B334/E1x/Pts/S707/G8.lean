import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J1216
import B334.E1x.Pts.S707.J1218
import B334.E1x.Pts.S707.J1222
import B334.E1x.Pts.S707.J1228
import B334.E1x.Pts.S707.J1250
import B334.E1x.Pts.S707.K1215L
import B334.E1x.Pts.S707.K1217L
import B334.E1x.Pts.S707.K1220L
import B334.E1x.Pts.S707.K1221L
import B334.E1x.Pts.S707.K1227L
import B334.E1x.Pts.S707.K1248L
import B334.E1x.Pts.S707.K1249L
import B334.E1x.Pts.S707.K1215Q0
import B334.E1x.Pts.S707.K1215Q1
import B334.E1x.Pts.S707.K1215Q2
import B334.E1x.Pts.S707.K1215Q3
import B334.E1x.Pts.S707.K1215Q4
import B334.E1x.Pts.S707.K1215Q5
import B334.E1x.Pts.S707.K1215Q6
import B334.E1x.Pts.S707.K1215Q7
import B334.E1x.Pts.S707.K1215Q8
import B334.E1x.Pts.S707.K1215Q9
import B334.E1x.Pts.S707.K1217Q0
import B334.E1x.Pts.S707.K1217Q1
import B334.E1x.Pts.S707.K1217Q2
import B334.E1x.Pts.S707.K1217Q3
import B334.E1x.Pts.S707.K1217Q4
import B334.E1x.Pts.S707.K1217Q5
import B334.E1x.Pts.S707.K1217Q6
import B334.E1x.Pts.S707.K1217Q7
import B334.E1x.Pts.S707.K1217Q8
import B334.E1x.Pts.S707.K1217Q9
import B334.E1x.Pts.S707.K1220Q0
import B334.E1x.Pts.S707.K1220Q1
import B334.E1x.Pts.S707.K1221Q0
import B334.E1x.Pts.S707.K1221Q1
import B334.E1x.Pts.S707.K1221Q2
import B334.E1x.Pts.S707.K1221Q3
import B334.E1x.Pts.S707.K1227Q0
import B334.E1x.Pts.S707.K1248Q0
import B334.E1x.Pts.S707.K1249Q0
import B334.E1x.Pts.S707.K1215Q10
import B334.E1x.Pts.S707.K1215Q11
import B334.E1x.Pts.S707.K1215Q12
import B334.E1x.Pts.S707.K1215Q13
import B334.E1x.Pts.S707.K1215Q14
import B334.E1x.Pts.S707.K1215Q15
import B334.E1x.Pts.S707.K1215Q16
import B334.E1x.Pts.S707.K1215Q17
import B334.E1x.Pts.S707.K1215Q18
import B334.E1x.Pts.S707.K1215Q19
import B334.E1x.Pts.S707.K1215Q20
import B334.E1x.Pts.S707.K1215Q21
import B334.E1x.Pts.S707.K1215Q22
import B334.E1x.Pts.S707.K1215Q23
import B334.E1x.Pts.S707.K1217Q10
import B334.E1x.Pts.S707.K1217Q11
import B334.E1x.Pts.S707.K1217Q12
import B334.E1x.Pts.S707.K1217Q13
import B334.E1x.Pts.S707.K1217Q14
import B334.E1x.Pts.S707.K1217Q15
import B334.E1x.Pts.S707.K1217Q16
import B334.E1x.Pts.S707.K1217Q17
import B334.E1x.Pts.S707.K1217Q18
import B334.E1x.Pts.S707.K1217Q19
import B334.E1x.Pts.S707.K1217Q20
import B334.E1x.Pts.S707.K1217Q21
import B334.E1x.Pts.S707.K1217Q22

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 1215 … 1251 (stage707_v6): the v5 Fin's job blocks r246 … r258 as
theorems, joined into `grp6_8` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_246 : ∀ k, 1215 ≤ k → k < 1216 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2147 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2 = true := kb_1215_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2 3 h0 kb_1215_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 5 6 h1 kb_1215_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 11 8 h2 kb_1215_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 19 8 h3 kb_1215_19
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 27 1 h4 kb_1215_27
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 28 1 h5 kb_1215_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 29 2 h6 kb_1215_29
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 31 1 h7 kb_1215_31
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 32 2 h8 kb_1215_32
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 34 2 h9 kb_1215_34
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 36 2 h10 kb_1215_36
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 38 10 h11 kb_1215_38
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 48 4 h12 kb_1215_48
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 52 5 h13 kb_1215_52
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 57 2 h14 kb_1215_57
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 59 1 h15 kb_1215_59
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 60 8 h16 kb_1215_60
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 68 2 h17 kb_1215_68
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 70 10 h18 kb_1215_70
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 80 1 h19 kb_1215_80
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 81 21 h20 kb_1215_81
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 102 10 h21 kb_1215_102
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 112 6 h22 kb_1215_112
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 118 2 h23 kb_1215_118
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 120 16 h24 kb_1215_120
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 136 2 h25 kb_1215_136
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 138 3 h26 kb_1215_138
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 141 6 h27 kb_1215_141
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 147 2 h28 kb_1215_147
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 149 18 h29 kb_1215_149
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 167 1 h30 kb_1215_167
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 168 1 h31 kb_1215_168
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 169 1 h32 kb_1215_169
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 170 1 h33 kb_1215_170
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 171 1 h34 kb_1215_171
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 172 2 h35 kb_1215_172
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 174 2 h36 kb_1215_174
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 176 4 h37 kb_1215_176
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 180 6 h38 kb_1215_180
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 186 3 h39 kb_1215_186
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 189 5 h40 kb_1215_189
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 194 2 h41 kb_1215_194
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 196 29 h42 kb_1215_196
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 225 2 h43 kb_1215_225
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 227 6 h44 kb_1215_227
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 233 3 h45 kb_1215_233
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 236 76 h46 kb_1215_236
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 312 14 h47 kb_1215_312
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 326 2 h48 kb_1215_326
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 328 11 h49 kb_1215_328
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 339 2 h50 kb_1215_339
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 341 3 h51 kb_1215_341
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 344 1 h52 kb_1215_344
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 345 6 h53 kb_1215_345
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 351 2 h54 kb_1215_351
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 353 16 h55 kb_1215_353
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 369 2 h56 kb_1215_369
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 371 2 h57 kb_1215_371
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 373 47 h58 kb_1215_373
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 490 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 420 70 h59 kb_1215_420
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 490 2 h60 kb_1215_490
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 521 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 492 29 h61 kb_1215_492
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 521 2 h62 kb_1215_521
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 523 6 h63 kb_1215_523
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 531 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 529 2 h64 kb_1215_529
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 531 22 h65 kb_1215_531
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 553 9 h66 kb_1215_553
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 562 23 h67 kb_1215_562
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 585 15 h68 kb_1215_585
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 600 8 h69 kb_1215_600
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 608 4 h70 kb_1215_608
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 631 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 612 19 h71 kb_1215_612
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 631 2 h72 kb_1215_631
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 633 23 h73 kb_1215_633
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 656 2 h74 kb_1215_656
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 658 12 h75 kb_1215_658
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 670 5 h76 kb_1215_670
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 675 5 h77 kb_1215_675
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 680 16 h78 kb_1215_680
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 698 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 696 2 h79 kb_1215_696
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 705 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 698 7 h80 kb_1215_698
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 705 2 h81 kb_1215_705
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 707 16 h82 kb_1215_707
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 725 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 723 2 h83 kb_1215_723
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 725 15 h84 kb_1215_725
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 740 1 h85 kb_1215_740
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 741 16 h86 kb_1215_741
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 757 1 h87 kb_1215_757
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 760 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 758 2 h88 kb_1215_758
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 764 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 760 4 h89 kb_1215_760
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 764 20 h90 kb_1215_764
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 784 7 h91 kb_1215_784
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 792 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 791 1 h92 kb_1215_791
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 792 1 h93 kb_1215_792
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 793 1 h94 kb_1215_793
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 795 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 794 1 h95 kb_1215_794
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 795 1 h96 kb_1215_795
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 796 2 h97 kb_1215_796
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 800 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 798 2 h98 kb_1215_798
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 800 2 h99 kb_1215_800
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 803 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 802 1 h100 kb_1215_802
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 805 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 803 2 h101 kb_1215_803
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 807 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 805 2 h102 kb_1215_805
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 816 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 807 9 h103 kb_1215_807
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 816 4 h104 kb_1215_816
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 821 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 820 1 h105 kb_1215_820
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 821 3 h106 kb_1215_821
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 824 4 h107 kb_1215_824
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 828 1 h108 kb_1215_828
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 829 15 h109 kb_1215_829
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 861 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 844 17 h110 kb_1215_844
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 861 6 h111 kb_1215_861
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 867 2 h112 kb_1215_867
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 869 52 h113 kb_1215_869
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 937 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 921 16 h114 kb_1215_921
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 959 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 937 22 h115 kb_1215_937
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 960 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 959 1 h116 kb_1215_959
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 960 12 h117 kb_1215_960
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 977 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 972 5 h118 kb_1215_972
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 977 1 h119 kb_1215_977
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 993 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 978 15 h120 kb_1215_978
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 993 1 h121 kb_1215_993
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1025 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 994 31 h122 kb_1215_994
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1041 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1025 16 h123 kb_1215_1025
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1041 2 h124 kb_1215_1041
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1054 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1043 11 h125 kb_1215_1043
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1055 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1054 1 h126 kb_1215_1054
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1066 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1055 11 h127 kb_1215_1055
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1066 2 h128 kb_1215_1066
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1068 36 h129 kb_1215_1068
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1104 1 h130 kb_1215_1104
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1105 2 h131 kb_1215_1105
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1107 1 h132 kb_1215_1107
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1108 1 h133 kb_1215_1108
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1109 20 h134 kb_1215_1109
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1129 7 h135 kb_1215_1129
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1136 1 h136 kb_1215_1136
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1137 3 h137 kb_1215_1137
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1140 5 h138 kb_1215_1140
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1145 4 h139 kb_1215_1145
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1149 1 h140 kb_1215_1149
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1150 9 h141 kb_1215_1150
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1159 6 h142 kb_1215_1159
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1165 1 h143 kb_1215_1165
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1166 9 h144 kb_1215_1166
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1175 2 h145 kb_1215_1175
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1177 4 h146 kb_1215_1177
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1181 1 h147 kb_1215_1181
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1182 8 h148 kb_1215_1182
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1190 2 h149 kb_1215_1190
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1192 4 h150 kb_1215_1192
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1196 8 h151 kb_1215_1196
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1204 2 h152 kb_1215_1204
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1206 9 h153 kb_1215_1206
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1215 1 h154 kb_1215_1215
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1216 7 h155 kb_1215_1216
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1223 2 h156 kb_1215_1223
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1225 3 h157 kb_1215_1225
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1228 16 h158 kb_1215_1228
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1244 2 h159 kb_1215_1244
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1246 22 h160 kb_1215_1246
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1268 2 h161 kb_1215_1268
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1270 1 h162 kb_1215_1270
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1295 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1271 24 h163 kb_1215_1271
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1295 18 h164 kb_1215_1295
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1313 27 h165 kb_1215_1313
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1340 11 h166 kb_1215_1340
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1351 22 h167 kb_1215_1351
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1373 2 h168 kb_1215_1373
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1375 10 h169 kb_1215_1375
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1385 13 h170 kb_1215_1385
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1398 13 h171 kb_1215_1398
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1411 2 h172 kb_1215_1411
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1413 12 h173 kb_1215_1413
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1425 2 h174 kb_1215_1425
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1441 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1427 14 h175 kb_1215_1427
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1441 10 h176 kb_1215_1441
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1451 2 h177 kb_1215_1451
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1453 1 h178 kb_1215_1453
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1454 1 h179 kb_1215_1454
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1456 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1455 1 h180 kb_1215_1455
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1456 1 h181 kb_1215_1456
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1459 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1457 2 h182 kb_1215_1457
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1462 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1459 3 h183 kb_1215_1459
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1462 7 h184 kb_1215_1462
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1478 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1469 9 h185 kb_1215_1469
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1478 3 h186 kb_1215_1478
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1481 5 h187 kb_1215_1481
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1486 1 h188 kb_1215_1486
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1487 7 h189 kb_1215_1487
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1494 1 h190 kb_1215_1494
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1495 7 h191 kb_1215_1495
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1502 3 h192 kb_1215_1502
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1505 1 h193 kb_1215_1505
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1506 9 h194 kb_1215_1506
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1515 1 h195 kb_1215_1515
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1516 21 h196 kb_1215_1516
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1537 3 h197 kb_1215_1537
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1540 26 h198 kb_1215_1540
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1566 23 h199 kb_1215_1566
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1595 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1589 6 h200 kb_1215_1589
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1595 8 h201 kb_1215_1595
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1637 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1603 34 h202 kb_1215_1603
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1637 1 h203 kb_1215_1637
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1638 22 h204 kb_1215_1638
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1754 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1660 94 h205 kb_1215_1660
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1755 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1754 1 h206 kb_1215_1754
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1755 3 h207 kb_1215_1755
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1758 35 h208 kb_1215_1758
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1795 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1793 2 h209 kb_1215_1793
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1801 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1795 6 h210 kb_1215_1795
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1803 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1801 2 h211 kb_1215_1801
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1803 27 h212 kb_1215_1803
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1888 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1830 58 h213 kb_1215_1830
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1889 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1888 1 h214 kb_1215_1888
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1890 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1889 1 h215 kb_1215_1889
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1897 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1890 7 h216 kb_1215_1890
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1905 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1897 8 h217 kb_1215_1897
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1911 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1905 6 h218 kb_1215_1905
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1911 9 h219 kb_1215_1911
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1920 7 h220 kb_1215_1920
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1927 5 h221 kb_1215_1927
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1940 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1932 8 h222 kb_1215_1932
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1950 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1940 10 h223 kb_1215_1940
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1951 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1950 1 h224 kb_1215_1950
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1951 4 h225 kb_1215_1951
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1955 10 h226 kb_1215_1955
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1968 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1965 3 h227 kb_1215_1965
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1973 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1968 5 h228 kb_1215_1968
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1973 1 h229 kb_1215_1973
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1974 4 h230 kb_1215_1974
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2015 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 1978 37 h231 kb_1215_1978
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2038 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2015 23 h232 kb_1215_2015
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2059 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2038 21 h233 kb_1215_2038
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2063 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2059 4 h234 kb_1215_2059
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2067 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2063 4 h235 kb_1215_2063
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2077 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2067 10 h236 kb_1215_2067
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2089 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2077 12 h237 kb_1215_2077
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2099 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2089 10 h238 kb_1215_2089
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2099 4 h239 kb_1215_2099
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2103 5 h240 kb_1215_2103
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2108 14 h241 kb_1215_2108
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2122 22 h242 kb_1215_2122
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1215.lits.getD i 0)) 0 2144 3 h243 kb_1215_2144
    exact h244
  have hg : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2147 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2 = true := kg_1215_0
    have h1 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 5 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2 3 h0 kg_1215_2
    have h2 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 11 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 5 6 h1 kg_1215_5
    have h3 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 19 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 11 8 h2 kg_1215_11
    have h4 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 27 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 19 8 h3 kg_1215_19
    have h5 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 28 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 27 1 h4 kg_1215_27
    have h6 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 29 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 28 1 h5 kg_1215_28
    have h7 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 31 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 29 2 h6 kg_1215_29
    have h8 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 32 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 31 1 h7 kg_1215_31
    have h9 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 34 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 32 2 h8 kg_1215_32
    have h10 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 36 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 34 2 h9 kg_1215_34
    have h11 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 38 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 36 2 h10 kg_1215_36
    have h12 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 48 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 38 10 h11 kg_1215_38
    have h13 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 52 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 48 4 h12 kg_1215_48
    have h14 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 57 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 52 5 h13 kg_1215_52
    have h15 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 59 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 57 2 h14 kg_1215_57
    have h16 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 60 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 59 1 h15 kg_1215_59
    have h17 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 68 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 60 8 h16 kg_1215_60
    have h18 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 70 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 68 2 h17 kg_1215_68
    have h19 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 80 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 70 10 h18 kg_1215_70
    have h20 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 81 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 80 1 h19 kg_1215_80
    have h21 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 102 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 81 21 h20 kg_1215_81
    have h22 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 112 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 102 10 h21 kg_1215_102
    have h23 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 118 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 112 6 h22 kg_1215_112
    have h24 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 120 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 118 2 h23 kg_1215_118
    have h25 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 136 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 120 16 h24 kg_1215_120
    have h26 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 138 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 136 2 h25 kg_1215_136
    have h27 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 141 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 138 3 h26 kg_1215_138
    have h28 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 147 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 141 6 h27 kg_1215_141
    have h29 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 149 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 147 2 h28 kg_1215_147
    have h30 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 167 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 149 18 h29 kg_1215_149
    have h31 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 168 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 167 1 h30 kg_1215_167
    have h32 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 169 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 168 1 h31 kg_1215_168
    have h33 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 170 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 169 1 h32 kg_1215_169
    have h34 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 171 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 170 1 h33 kg_1215_170
    have h35 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 172 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 171 1 h34 kg_1215_171
    have h36 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 174 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 172 2 h35 kg_1215_172
    have h37 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 176 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 174 2 h36 kg_1215_174
    have h38 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 180 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 176 4 h37 kg_1215_176
    have h39 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 186 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 180 6 h38 kg_1215_180
    have h40 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 189 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 186 3 h39 kg_1215_186
    have h41 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 194 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 189 5 h40 kg_1215_189
    have h42 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 196 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 194 2 h41 kg_1215_194
    have h43 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 225 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 196 29 h42 kg_1215_196
    have h44 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 227 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 225 2 h43 kg_1215_225
    have h45 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 233 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 227 6 h44 kg_1215_227
    have h46 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 236 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 233 3 h45 kg_1215_233
    have h47 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 312 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 236 76 h46 kg_1215_236
    have h48 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 326 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 312 14 h47 kg_1215_312
    have h49 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 328 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 326 2 h48 kg_1215_326
    have h50 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 339 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 328 11 h49 kg_1215_328
    have h51 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 341 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 339 2 h50 kg_1215_339
    have h52 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 344 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 341 3 h51 kg_1215_341
    have h53 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 345 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 344 1 h52 kg_1215_344
    have h54 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 351 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 345 6 h53 kg_1215_345
    have h55 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 353 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 351 2 h54 kg_1215_351
    have h56 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 369 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 353 16 h55 kg_1215_353
    have h57 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 371 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 369 2 h56 kg_1215_369
    have h58 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 373 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 371 2 h57 kg_1215_371
    have h59 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 420 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 373 47 h58 kg_1215_373
    have h60 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 490 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 420 70 h59 kg_1215_420
    have h61 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 492 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 490 2 h60 kg_1215_490
    have h62 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 521 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 492 29 h61 kg_1215_492
    have h63 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 523 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 521 2 h62 kg_1215_521
    have h64 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 529 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 523 6 h63 kg_1215_523
    have h65 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 531 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 529 2 h64 kg_1215_529
    have h66 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 553 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 531 22 h65 kg_1215_531
    have h67 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 562 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 553 9 h66 kg_1215_553
    have h68 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 585 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 562 23 h67 kg_1215_562
    have h69 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 600 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 585 15 h68 kg_1215_585
    have h70 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 608 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 600 8 h69 kg_1215_600
    have h71 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 612 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 608 4 h70 kg_1215_608
    have h72 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 631 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 612 19 h71 kg_1215_612
    have h73 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 633 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 631 2 h72 kg_1215_631
    have h74 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 656 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 633 23 h73 kg_1215_633
    have h75 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 658 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 656 2 h74 kg_1215_656
    have h76 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 670 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 658 12 h75 kg_1215_658
    have h77 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 675 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 670 5 h76 kg_1215_670
    have h78 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 680 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 675 5 h77 kg_1215_675
    have h79 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 696 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 680 16 h78 kg_1215_680
    have h80 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 698 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 696 2 h79 kg_1215_696
    have h81 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 705 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 698 7 h80 kg_1215_698
    have h82 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 707 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 705 2 h81 kg_1215_705
    have h83 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 723 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 707 16 h82 kg_1215_707
    have h84 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 725 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 723 2 h83 kg_1215_723
    have h85 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 740 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 725 15 h84 kg_1215_725
    have h86 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 741 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 740 1 h85 kg_1215_740
    have h87 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 757 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 741 16 h86 kg_1215_741
    have h88 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 758 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 757 1 h87 kg_1215_757
    have h89 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 760 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 758 2 h88 kg_1215_758
    have h90 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 764 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 760 4 h89 kg_1215_760
    have h91 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 784 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 764 20 h90 kg_1215_764
    have h92 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 791 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 784 7 h91 kg_1215_784
    have h93 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 792 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 791 1 h92 kg_1215_791
    have h94 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 793 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 792 1 h93 kg_1215_792
    have h95 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 794 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 793 1 h94 kg_1215_793
    have h96 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 795 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 794 1 h95 kg_1215_794
    have h97 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 796 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 795 1 h96 kg_1215_795
    have h98 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 798 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 796 2 h97 kg_1215_796
    have h99 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 800 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 798 2 h98 kg_1215_798
    have h100 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 802 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 800 2 h99 kg_1215_800
    have h101 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 803 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 802 1 h100 kg_1215_802
    have h102 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 805 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 803 2 h101 kg_1215_803
    have h103 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 807 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 805 2 h102 kg_1215_805
    have h104 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 816 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 807 9 h103 kg_1215_807
    have h105 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 820 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 816 4 h104 kg_1215_816
    have h106 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 821 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 820 1 h105 kg_1215_820
    have h107 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 824 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 821 3 h106 kg_1215_821
    have h108 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 828 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 824 4 h107 kg_1215_824
    have h109 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 829 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 828 1 h108 kg_1215_828
    have h110 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 844 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 829 15 h109 kg_1215_829
    have h111 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 861 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 844 17 h110 kg_1215_844
    have h112 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 867 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 861 6 h111 kg_1215_861
    have h113 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 869 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 867 2 h112 kg_1215_867
    have h114 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 921 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 869 52 h113 kg_1215_869
    have h115 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 937 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 921 16 h114 kg_1215_921
    have h116 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 959 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 937 22 h115 kg_1215_937
    have h117 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 960 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 959 1 h116 kg_1215_959
    have h118 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 972 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 960 12 h117 kg_1215_960
    have h119 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 977 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 972 5 h118 kg_1215_972
    have h120 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 978 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 977 1 h119 kg_1215_977
    have h121 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 993 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 978 15 h120 kg_1215_978
    have h122 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 994 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 993 1 h121 kg_1215_993
    have h123 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1025 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 994 31 h122 kg_1215_994
    have h124 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1041 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1025 16 h123 kg_1215_1025
    have h125 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1043 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1041 2 h124 kg_1215_1041
    have h126 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1054 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1043 11 h125 kg_1215_1043
    have h127 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1055 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1054 1 h126 kg_1215_1054
    have h128 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1066 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1055 11 h127 kg_1215_1055
    have h129 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1068 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1066 2 h128 kg_1215_1066
    have h130 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1104 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1068 36 h129 kg_1215_1068
    have h131 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1105 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1104 1 h130 kg_1215_1104
    have h132 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1107 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1105 2 h131 kg_1215_1105
    have h133 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1108 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1107 1 h132 kg_1215_1107
    have h134 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1109 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1108 1 h133 kg_1215_1108
    have h135 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1129 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1109 20 h134 kg_1215_1109
    have h136 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1136 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1129 7 h135 kg_1215_1129
    have h137 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1137 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1136 1 h136 kg_1215_1136
    have h138 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1140 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1137 3 h137 kg_1215_1137
    have h139 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1145 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1140 5 h138 kg_1215_1140
    have h140 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1149 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1145 4 h139 kg_1215_1145
    have h141 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1150 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1149 1 h140 kg_1215_1149
    have h142 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1159 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1150 9 h141 kg_1215_1150
    have h143 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1165 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1159 6 h142 kg_1215_1159
    have h144 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1166 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1165 1 h143 kg_1215_1165
    have h145 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1175 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1166 9 h144 kg_1215_1166
    have h146 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1177 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1175 2 h145 kg_1215_1175
    have h147 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1181 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1177 4 h146 kg_1215_1177
    have h148 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1182 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1181 1 h147 kg_1215_1181
    have h149 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1190 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1182 8 h148 kg_1215_1182
    have h150 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1192 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1190 2 h149 kg_1215_1190
    have h151 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1196 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1192 4 h150 kg_1215_1192
    have h152 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1204 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1196 8 h151 kg_1215_1196
    have h153 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1206 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1204 2 h152 kg_1215_1204
    have h154 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1215 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1206 9 h153 kg_1215_1206
    have h155 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1216 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1215 1 h154 kg_1215_1215
    have h156 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1223 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1216 7 h155 kg_1215_1216
    have h157 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1225 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1223 2 h156 kg_1215_1223
    have h158 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1228 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1225 3 h157 kg_1215_1225
    have h159 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1244 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1228 16 h158 kg_1215_1228
    have h160 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1246 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1244 2 h159 kg_1215_1244
    have h161 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1268 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1246 22 h160 kg_1215_1246
    have h162 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1270 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1268 2 h161 kg_1215_1268
    have h163 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1271 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1270 1 h162 kg_1215_1270
    have h164 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1295 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1271 24 h163 kg_1215_1271
    have h165 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1313 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1295 18 h164 kg_1215_1295
    have h166 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1340 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1313 27 h165 kg_1215_1313
    have h167 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1351 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1340 11 h166 kg_1215_1340
    have h168 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1373 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1351 22 h167 kg_1215_1351
    have h169 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1375 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1373 2 h168 kg_1215_1373
    have h170 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1385 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1375 10 h169 kg_1215_1375
    have h171 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1398 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1385 13 h170 kg_1215_1385
    have h172 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1411 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1398 13 h171 kg_1215_1398
    have h173 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1413 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1411 2 h172 kg_1215_1411
    have h174 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1425 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1413 12 h173 kg_1215_1413
    have h175 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1427 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1425 2 h174 kg_1215_1425
    have h176 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1441 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1427 14 h175 kg_1215_1427
    have h177 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1451 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1441 10 h176 kg_1215_1441
    have h178 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1453 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1451 2 h177 kg_1215_1451
    have h179 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1454 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1453 1 h178 kg_1215_1453
    have h180 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1455 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1454 1 h179 kg_1215_1454
    have h181 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1456 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1455 1 h180 kg_1215_1455
    have h182 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1457 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1456 1 h181 kg_1215_1456
    have h183 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1459 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1457 2 h182 kg_1215_1457
    have h184 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1462 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1459 3 h183 kg_1215_1459
    have h185 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1469 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1462 7 h184 kg_1215_1462
    have h186 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1478 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1469 9 h185 kg_1215_1469
    have h187 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1481 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1478 3 h186 kg_1215_1478
    have h188 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1486 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1481 5 h187 kg_1215_1481
    have h189 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1487 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1486 1 h188 kg_1215_1486
    have h190 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1494 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1487 7 h189 kg_1215_1487
    have h191 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1495 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1494 1 h190 kg_1215_1494
    have h192 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1502 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1495 7 h191 kg_1215_1495
    have h193 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1505 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1502 3 h192 kg_1215_1502
    have h194 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1506 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1505 1 h193 kg_1215_1505
    have h195 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1515 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1506 9 h194 kg_1215_1506
    have h196 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1516 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1515 1 h195 kg_1215_1515
    have h197 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1537 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1516 21 h196 kg_1215_1516
    have h198 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1540 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1537 3 h197 kg_1215_1537
    have h199 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1566 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1540 26 h198 kg_1215_1540
    have h200 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1589 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1566 23 h199 kg_1215_1566
    have h201 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1595 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1589 6 h200 kg_1215_1589
    have h202 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1603 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1595 8 h201 kg_1215_1595
    have h203 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1637 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1603 34 h202 kg_1215_1603
    have h204 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1638 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1637 1 h203 kg_1215_1637
    have h205 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1660 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1638 22 h204 kg_1215_1638
    have h206 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1754 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1660 94 h205 kg_1215_1660
    have h207 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1755 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1754 1 h206 kg_1215_1754
    have h208 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1758 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1755 3 h207 kg_1215_1755
    have h209 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1793 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1758 35 h208 kg_1215_1758
    have h210 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1795 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1793 2 h209 kg_1215_1793
    have h211 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1801 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1795 6 h210 kg_1215_1795
    have h212 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1803 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1801 2 h211 kg_1215_1801
    have h213 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1830 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1803 27 h212 kg_1215_1803
    have h214 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1888 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1830 58 h213 kg_1215_1830
    have h215 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1889 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1888 1 h214 kg_1215_1888
    have h216 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1890 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1889 1 h215 kg_1215_1889
    have h217 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1897 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1890 7 h216 kg_1215_1890
    have h218 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1905 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1897 8 h217 kg_1215_1897
    have h219 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1911 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1905 6 h218 kg_1215_1905
    have h220 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1920 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1911 9 h219 kg_1215_1911
    have h221 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1927 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1920 7 h220 kg_1215_1920
    have h222 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1932 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1927 5 h221 kg_1215_1927
    have h223 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1940 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1932 8 h222 kg_1215_1932
    have h224 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1950 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1940 10 h223 kg_1215_1940
    have h225 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1951 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1950 1 h224 kg_1215_1950
    have h226 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1955 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1951 4 h225 kg_1215_1951
    have h227 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1965 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1955 10 h226 kg_1215_1955
    have h228 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1968 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1965 3 h227 kg_1215_1965
    have h229 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1973 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1968 5 h228 kg_1215_1968
    have h230 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1974 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1973 1 h229 kg_1215_1973
    have h231 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 1978 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1974 4 h230 kg_1215_1974
    have h232 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2015 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 1978 37 h231 kg_1215_1978
    have h233 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2038 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2015 23 h232 kg_1215_2015
    have h234 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2059 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2038 21 h233 kg_1215_2038
    have h235 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2063 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2059 4 h234 kg_1215_2059
    have h236 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2067 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2063 4 h235 kg_1215_2063
    have h237 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2077 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2067 10 h236 kg_1215_2067
    have h238 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2089 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2077 12 h237 kg_1215_2077
    have h239 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2099 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2089 10 h238 kg_1215_2089
    have h240 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2103 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2099 4 h239 kg_1215_2099
    have h241 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2108 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2103 5 h240 kg_1215_2103
    have h242 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2122 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2108 14 h241 kg_1215_2108
    have h243 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2144 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2122 22 h242 kg_1215_2122
    have h244 : IPChk.allR (Pts.glueIB K1215.lits KW_1215) 0 2147 = true := IPChk.allR_join (Pts.glueIB K1215.lits KW_1215) 0 2144 3 h243 kg_1215_2144
    exact h244
  have hlen : K1215.lits.length = 2147 := by decide
  intro k h1 h2
  obtain rfl : k = 1215 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1215) K1215.lits KW_1215
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_247 : ∀ k, 1216 ≤ k → k < 1217 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1216 JW_1216 1216 1 jr_1216
theorem jr6_248 : ∀ k, 1217 ≤ k → k < 1218 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1767 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 3 = true := kb_1217_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 3 3 h0 kb_1217_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 6 2 h1 kb_1217_6
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 8 4 h2 kb_1217_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 12 11 h3 kb_1217_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 23 3 h4 kb_1217_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 26 2 h5 kb_1217_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 28 1 h6 kb_1217_28
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 29 14 h7 kb_1217_29
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 43 10 h8 kb_1217_43
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 53 6 h9 kb_1217_53
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 59 2 h10 kb_1217_59
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 61 1 h11 kb_1217_61
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 62 1 h12 kb_1217_62
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 63 13 h13 kb_1217_63
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 76 18 h14 kb_1217_76
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 94 6 h15 kb_1217_94
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 100 2 h16 kb_1217_100
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 102 22 h17 kb_1217_102
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 124 5 h18 kb_1217_124
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 129 45 h19 kb_1217_129
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 174 6 h20 kb_1217_174
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 180 2 h21 kb_1217_180
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 182 15 h22 kb_1217_182
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 197 2 h23 kb_1217_197
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 199 2 h24 kb_1217_199
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 201 2 h25 kb_1217_201
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 203 1 h26 kb_1217_203
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 204 3 h27 kb_1217_204
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 207 2 h28 kb_1217_207
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 209 29 h29 kb_1217_209
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 238 2 h30 kb_1217_238
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 240 6 h31 kb_1217_240
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 246 2 h32 kb_1217_246
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 248 62 h33 kb_1217_248
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 310 20 h34 kb_1217_310
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 330 36 h35 kb_1217_330
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 366 1 h36 kb_1217_366
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 367 1 h37 kb_1217_367
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 368 13 h38 kb_1217_368
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 381 1 h39 kb_1217_381
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 382 3 h40 kb_1217_382
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 386 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 385 1 h41 kb_1217_385
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 386 6 h42 kb_1217_386
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 394 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 392 2 h43 kb_1217_392
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 394 2 h44 kb_1217_394
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 396 3 h45 kb_1217_396
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 399 7 h46 kb_1217_399
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 406 6 h47 kb_1217_406
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 412 1 h48 kb_1217_412
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 413 2 h49 kb_1217_413
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 415 2 h50 kb_1217_415
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 417 2 h51 kb_1217_417
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 419 4 h52 kb_1217_419
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 423 8 h53 kb_1217_423
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 431 19 h54 kb_1217_431
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 450 2 h55 kb_1217_450
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 452 22 h56 kb_1217_452
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 474 2 h57 kb_1217_474
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 476 12 h58 kb_1217_476
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 488 3 h59 kb_1217_488
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 491 6 h60 kb_1217_491
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 498 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 497 1 h61 kb_1217_497
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 513 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 498 15 h62 kb_1217_498
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 513 2 h63 kb_1217_513
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 515 8 h64 kb_1217_515
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 523 16 h65 kb_1217_523
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 541 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 539 2 h66 kb_1217_539
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 541 15 h67 kb_1217_541
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 556 4 h68 kb_1217_556
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 560 5 h69 kb_1217_560
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 565 11 h70 kb_1217_565
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 576 3 h71 kb_1217_576
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 579 1 h72 kb_1217_579
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 594 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 580 14 h73 kb_1217_580
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 599 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 594 5 h74 kb_1217_594
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 599 1 h75 kb_1217_599
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 600 1 h76 kb_1217_600
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 601 2 h77 kb_1217_601
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 603 6 h78 kb_1217_603
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 609 2 h79 kb_1217_609
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 611 1 h80 kb_1217_611
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 612 1 h81 kb_1217_612
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 613 29 h82 kb_1217_613
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 642 2 h83 kb_1217_642
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 644 6 h84 kb_1217_644
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 650 2 h85 kb_1217_650
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 652 63 h86 kb_1217_652
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 715 19 h87 kb_1217_715
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 734 1 h88 kb_1217_734
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 737 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 735 2 h89 kb_1217_735
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 737 20 h90 kb_1217_737
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 757 4 h91 kb_1217_757
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 761 9 h92 kb_1217_761
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 770 1 h93 kb_1217_770
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 771 14 h94 kb_1217_771
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 785 1 h95 kb_1217_785
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 786 18 h96 kb_1217_786
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 804 18 h97 kb_1217_804
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 822 1 h98 kb_1217_822
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 823 11 h99 kb_1217_823
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 837 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 834 3 h100 kb_1217_834
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 839 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 837 2 h101 kb_1217_837
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 849 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 839 10 h102 kb_1217_839
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 850 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 849 1 h103 kb_1217_849
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 856 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 850 6 h104 kb_1217_850
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 856 6 h105 kb_1217_856
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 863 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 862 1 h106 kb_1217_862
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 863 6 h107 kb_1217_863
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 870 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 869 1 h108 kb_1217_869
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 871 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 870 1 h109 kb_1217_870
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 874 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 871 3 h110 kb_1217_871
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 874 1 h111 kb_1217_874
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 881 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 875 6 h112 kb_1217_875
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 882 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 881 1 h113 kb_1217_881
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 884 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 882 2 h114 kb_1217_882
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 884 2 h115 kb_1217_884
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 890 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 886 4 h116 kb_1217_886
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 896 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 890 6 h117 kb_1217_890
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 898 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 896 2 h118 kb_1217_896
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 905 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 898 7 h119 kb_1217_898
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 906 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 905 1 h120 kb_1217_905
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 907 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 906 1 h121 kb_1217_906
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 908 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 907 1 h122 kb_1217_907
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 908 6 h123 kb_1217_908
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 916 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 914 2 h124 kb_1217_914
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 918 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 916 2 h125 kb_1217_916
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 918 2 h126 kb_1217_918
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 920 1 h127 kb_1217_920
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 923 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 921 2 h128 kb_1217_921
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 925 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 923 2 h129 kb_1217_923
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 930 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 925 5 h130 kb_1217_925
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 931 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 930 1 h131 kb_1217_930
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 931 4 h132 kb_1217_931
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 935 1 h133 kb_1217_935
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 937 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 936 1 h134 kb_1217_936
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 939 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 937 2 h135 kb_1217_937
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 939 19 h136 kb_1217_939
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 971 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 958 13 h137 kb_1217_958
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 977 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 971 6 h138 kb_1217_971
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1027 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 977 50 h139 kb_1217_977
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1048 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1027 21 h140 kb_1217_1027
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1049 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1048 1 h141 kb_1217_1048
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1049 22 h142 kb_1217_1049
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1071 32 h143 kb_1217_1071
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1103 13 h144 kb_1217_1103
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1116 1 h145 kb_1217_1116
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1117 11 h146 kb_1217_1117
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1128 8 h147 kb_1217_1128
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1136 12 h148 kb_1217_1136
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1148 6 h149 kb_1217_1148
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1154 1 h150 kb_1217_1154
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1155 11 h151 kb_1217_1155
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1166 8 h152 kb_1217_1166
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1174 2 h153 kb_1217_1174
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1176 11 h154 kb_1217_1176
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1187 2 h155 kb_1217_1187
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1189 4 h156 kb_1217_1189
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1193 9 h157 kb_1217_1193
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1202 1 h158 kb_1217_1202
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1203 2 h159 kb_1217_1203
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1205 9 h160 kb_1217_1205
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1214 7 h161 kb_1217_1214
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1221 5 h162 kb_1217_1221
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1226 2 h163 kb_1217_1226
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1228 2 h164 kb_1217_1228
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1230 2 h165 kb_1217_1230
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1232 1 h166 kb_1217_1232
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1233 1 h167 kb_1217_1233
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1234 1 h168 kb_1217_1234
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1235 5 h169 kb_1217_1235
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1240 1 h170 kb_1217_1240
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1241 1 h171 kb_1217_1241
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1242 2 h172 kb_1217_1242
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1244 1 h173 kb_1217_1244
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1245 1 h174 kb_1217_1245
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1246 1 h175 kb_1217_1246
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1247 1 h176 kb_1217_1247
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1248 1 h177 kb_1217_1248
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1249 1 h178 kb_1217_1249
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1250 1 h179 kb_1217_1250
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1251 18 h180 kb_1217_1251
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1269 98 h181 kb_1217_1269
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1367 1 h182 kb_1217_1367
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1368 1 h183 kb_1217_1368
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1369 14 h184 kb_1217_1369
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1461 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1383 78 h185 kb_1217_1383
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1461 53 h186 kb_1217_1461
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1514 3 h187 kb_1217_1514
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1531 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1517 14 h188 kb_1217_1517
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1531 1 h189 kb_1217_1531
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1532 2 h190 kb_1217_1532
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1534 4 h191 kb_1217_1534
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1543 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1538 5 h192 kb_1217_1538
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1543 1 h193 kb_1217_1543
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1544 7 h194 kb_1217_1544
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1551 8 h195 kb_1217_1551
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1559 5 h196 kb_1217_1559
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1564 8 h197 kb_1217_1564
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1572 1 h198 kb_1217_1572
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1573 3 h199 kb_1217_1573
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1577 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1576 1 h200 kb_1217_1576
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1577 5 h201 kb_1217_1577
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1582 3 h202 kb_1217_1582
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1592 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1585 7 h203 kb_1217_1585
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1595 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1592 3 h204 kb_1217_1592
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1595 5 h205 kb_1217_1595
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1600 2 h206 kb_1217_1600
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1604 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1602 2 h207 kb_1217_1602
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1604 6 h208 kb_1217_1604
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1610 1 h209 kb_1217_1610
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1611 2 h210 kb_1217_1611
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1613 3 h211 kb_1217_1613
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1621 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1616 5 h212 kb_1217_1616
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1621 1 h213 kb_1217_1621
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1622 2 h214 kb_1217_1622
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1625 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1624 1 h215 kb_1217_1624
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1627 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1625 2 h216 kb_1217_1625
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1632 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1627 5 h217 kb_1217_1627
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1632 3 h218 kb_1217_1632
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1635 3 h219 kb_1217_1635
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1641 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1638 3 h220 kb_1217_1638
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1641 2 h221 kb_1217_1641
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1643 13 h222 kb_1217_1643
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1694 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1656 38 h223 kb_1217_1656
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1712 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1694 18 h224 kb_1217_1694
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1712 8 h225 kb_1217_1712
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1721 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1720 1 h226 kb_1217_1720
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1721 1 h227 kb_1217_1721
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1722 1 h228 kb_1217_1722
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1723 1 h229 kb_1217_1723
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1725 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1724 1 h230 kb_1217_1724
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1725 1 h231 kb_1217_1725
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1727 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1726 1 h232 kb_1217_1726
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1729 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1727 2 h233 kb_1217_1727
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1729 2 h234 kb_1217_1729
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1753 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1731 22 h235 kb_1217_1731
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1760 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1753 7 h236 kb_1217_1753
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1766 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1760 6 h237 kb_1217_1760
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1217.lits.getD i 0)) 0 1766 1 h238 kb_1217_1766
    exact h239
  have hg : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1767 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 3 = true := kg_1217_0
    have h1 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 6 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 3 3 h0 kg_1217_3
    have h2 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 8 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 6 2 h1 kg_1217_6
    have h3 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 12 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 8 4 h2 kg_1217_8
    have h4 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 23 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 12 11 h3 kg_1217_12
    have h5 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 26 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 23 3 h4 kg_1217_23
    have h6 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 28 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 26 2 h5 kg_1217_26
    have h7 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 29 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 28 1 h6 kg_1217_28
    have h8 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 43 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 29 14 h7 kg_1217_29
    have h9 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 53 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 43 10 h8 kg_1217_43
    have h10 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 59 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 53 6 h9 kg_1217_53
    have h11 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 61 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 59 2 h10 kg_1217_59
    have h12 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 62 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 61 1 h11 kg_1217_61
    have h13 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 63 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 62 1 h12 kg_1217_62
    have h14 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 76 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 63 13 h13 kg_1217_63
    have h15 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 94 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 76 18 h14 kg_1217_76
    have h16 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 100 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 94 6 h15 kg_1217_94
    have h17 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 102 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 100 2 h16 kg_1217_100
    have h18 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 124 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 102 22 h17 kg_1217_102
    have h19 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 129 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 124 5 h18 kg_1217_124
    have h20 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 174 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 129 45 h19 kg_1217_129
    have h21 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 180 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 174 6 h20 kg_1217_174
    have h22 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 182 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 180 2 h21 kg_1217_180
    have h23 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 197 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 182 15 h22 kg_1217_182
    have h24 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 199 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 197 2 h23 kg_1217_197
    have h25 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 201 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 199 2 h24 kg_1217_199
    have h26 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 203 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 201 2 h25 kg_1217_201
    have h27 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 204 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 203 1 h26 kg_1217_203
    have h28 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 207 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 204 3 h27 kg_1217_204
    have h29 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 209 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 207 2 h28 kg_1217_207
    have h30 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 238 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 209 29 h29 kg_1217_209
    have h31 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 240 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 238 2 h30 kg_1217_238
    have h32 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 246 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 240 6 h31 kg_1217_240
    have h33 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 248 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 246 2 h32 kg_1217_246
    have h34 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 310 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 248 62 h33 kg_1217_248
    have h35 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 330 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 310 20 h34 kg_1217_310
    have h36 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 366 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 330 36 h35 kg_1217_330
    have h37 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 367 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 366 1 h36 kg_1217_366
    have h38 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 368 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 367 1 h37 kg_1217_367
    have h39 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 381 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 368 13 h38 kg_1217_368
    have h40 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 382 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 381 1 h39 kg_1217_381
    have h41 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 385 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 382 3 h40 kg_1217_382
    have h42 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 386 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 385 1 h41 kg_1217_385
    have h43 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 392 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 386 6 h42 kg_1217_386
    have h44 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 394 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 392 2 h43 kg_1217_392
    have h45 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 396 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 394 2 h44 kg_1217_394
    have h46 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 399 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 396 3 h45 kg_1217_396
    have h47 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 406 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 399 7 h46 kg_1217_399
    have h48 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 412 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 406 6 h47 kg_1217_406
    have h49 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 413 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 412 1 h48 kg_1217_412
    have h50 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 415 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 413 2 h49 kg_1217_413
    have h51 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 417 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 415 2 h50 kg_1217_415
    have h52 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 419 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 417 2 h51 kg_1217_417
    have h53 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 423 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 419 4 h52 kg_1217_419
    have h54 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 431 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 423 8 h53 kg_1217_423
    have h55 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 450 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 431 19 h54 kg_1217_431
    have h56 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 452 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 450 2 h55 kg_1217_450
    have h57 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 474 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 452 22 h56 kg_1217_452
    have h58 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 476 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 474 2 h57 kg_1217_474
    have h59 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 488 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 476 12 h58 kg_1217_476
    have h60 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 491 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 488 3 h59 kg_1217_488
    have h61 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 497 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 491 6 h60 kg_1217_491
    have h62 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 498 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 497 1 h61 kg_1217_497
    have h63 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 513 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 498 15 h62 kg_1217_498
    have h64 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 515 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 513 2 h63 kg_1217_513
    have h65 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 523 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 515 8 h64 kg_1217_515
    have h66 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 539 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 523 16 h65 kg_1217_523
    have h67 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 541 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 539 2 h66 kg_1217_539
    have h68 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 556 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 541 15 h67 kg_1217_541
    have h69 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 560 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 556 4 h68 kg_1217_556
    have h70 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 565 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 560 5 h69 kg_1217_560
    have h71 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 576 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 565 11 h70 kg_1217_565
    have h72 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 579 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 576 3 h71 kg_1217_576
    have h73 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 580 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 579 1 h72 kg_1217_579
    have h74 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 594 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 580 14 h73 kg_1217_580
    have h75 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 599 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 594 5 h74 kg_1217_594
    have h76 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 600 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 599 1 h75 kg_1217_599
    have h77 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 601 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 600 1 h76 kg_1217_600
    have h78 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 603 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 601 2 h77 kg_1217_601
    have h79 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 609 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 603 6 h78 kg_1217_603
    have h80 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 611 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 609 2 h79 kg_1217_609
    have h81 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 612 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 611 1 h80 kg_1217_611
    have h82 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 613 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 612 1 h81 kg_1217_612
    have h83 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 642 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 613 29 h82 kg_1217_613
    have h84 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 644 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 642 2 h83 kg_1217_642
    have h85 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 650 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 644 6 h84 kg_1217_644
    have h86 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 652 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 650 2 h85 kg_1217_650
    have h87 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 715 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 652 63 h86 kg_1217_652
    have h88 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 734 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 715 19 h87 kg_1217_715
    have h89 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 735 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 734 1 h88 kg_1217_734
    have h90 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 737 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 735 2 h89 kg_1217_735
    have h91 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 757 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 737 20 h90 kg_1217_737
    have h92 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 761 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 757 4 h91 kg_1217_757
    have h93 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 770 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 761 9 h92 kg_1217_761
    have h94 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 771 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 770 1 h93 kg_1217_770
    have h95 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 785 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 771 14 h94 kg_1217_771
    have h96 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 786 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 785 1 h95 kg_1217_785
    have h97 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 804 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 786 18 h96 kg_1217_786
    have h98 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 822 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 804 18 h97 kg_1217_804
    have h99 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 823 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 822 1 h98 kg_1217_822
    have h100 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 834 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 823 11 h99 kg_1217_823
    have h101 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 837 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 834 3 h100 kg_1217_834
    have h102 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 839 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 837 2 h101 kg_1217_837
    have h103 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 849 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 839 10 h102 kg_1217_839
    have h104 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 850 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 849 1 h103 kg_1217_849
    have h105 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 856 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 850 6 h104 kg_1217_850
    have h106 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 862 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 856 6 h105 kg_1217_856
    have h107 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 863 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 862 1 h106 kg_1217_862
    have h108 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 869 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 863 6 h107 kg_1217_863
    have h109 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 870 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 869 1 h108 kg_1217_869
    have h110 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 871 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 870 1 h109 kg_1217_870
    have h111 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 874 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 871 3 h110 kg_1217_871
    have h112 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 875 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 874 1 h111 kg_1217_874
    have h113 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 881 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 875 6 h112 kg_1217_875
    have h114 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 882 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 881 1 h113 kg_1217_881
    have h115 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 884 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 882 2 h114 kg_1217_882
    have h116 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 886 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 884 2 h115 kg_1217_884
    have h117 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 890 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 886 4 h116 kg_1217_886
    have h118 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 896 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 890 6 h117 kg_1217_890
    have h119 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 898 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 896 2 h118 kg_1217_896
    have h120 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 905 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 898 7 h119 kg_1217_898
    have h121 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 906 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 905 1 h120 kg_1217_905
    have h122 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 907 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 906 1 h121 kg_1217_906
    have h123 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 908 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 907 1 h122 kg_1217_907
    have h124 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 914 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 908 6 h123 kg_1217_908
    have h125 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 916 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 914 2 h124 kg_1217_914
    have h126 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 918 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 916 2 h125 kg_1217_916
    have h127 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 920 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 918 2 h126 kg_1217_918
    have h128 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 921 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 920 1 h127 kg_1217_920
    have h129 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 923 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 921 2 h128 kg_1217_921
    have h130 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 925 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 923 2 h129 kg_1217_923
    have h131 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 930 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 925 5 h130 kg_1217_925
    have h132 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 931 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 930 1 h131 kg_1217_930
    have h133 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 935 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 931 4 h132 kg_1217_931
    have h134 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 936 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 935 1 h133 kg_1217_935
    have h135 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 937 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 936 1 h134 kg_1217_936
    have h136 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 939 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 937 2 h135 kg_1217_937
    have h137 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 958 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 939 19 h136 kg_1217_939
    have h138 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 971 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 958 13 h137 kg_1217_958
    have h139 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 977 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 971 6 h138 kg_1217_971
    have h140 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1027 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 977 50 h139 kg_1217_977
    have h141 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1048 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1027 21 h140 kg_1217_1027
    have h142 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1049 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1048 1 h141 kg_1217_1048
    have h143 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1071 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1049 22 h142 kg_1217_1049
    have h144 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1103 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1071 32 h143 kg_1217_1071
    have h145 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1116 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1103 13 h144 kg_1217_1103
    have h146 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1117 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1116 1 h145 kg_1217_1116
    have h147 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1128 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1117 11 h146 kg_1217_1117
    have h148 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1136 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1128 8 h147 kg_1217_1128
    have h149 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1148 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1136 12 h148 kg_1217_1136
    have h150 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1154 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1148 6 h149 kg_1217_1148
    have h151 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1155 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1154 1 h150 kg_1217_1154
    have h152 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1166 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1155 11 h151 kg_1217_1155
    have h153 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1174 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1166 8 h152 kg_1217_1166
    have h154 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1176 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1174 2 h153 kg_1217_1174
    have h155 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1187 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1176 11 h154 kg_1217_1176
    have h156 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1189 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1187 2 h155 kg_1217_1187
    have h157 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1193 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1189 4 h156 kg_1217_1189
    have h158 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1202 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1193 9 h157 kg_1217_1193
    have h159 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1203 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1202 1 h158 kg_1217_1202
    have h160 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1205 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1203 2 h159 kg_1217_1203
    have h161 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1214 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1205 9 h160 kg_1217_1205
    have h162 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1221 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1214 7 h161 kg_1217_1214
    have h163 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1226 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1221 5 h162 kg_1217_1221
    have h164 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1228 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1226 2 h163 kg_1217_1226
    have h165 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1230 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1228 2 h164 kg_1217_1228
    have h166 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1232 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1230 2 h165 kg_1217_1230
    have h167 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1233 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1232 1 h166 kg_1217_1232
    have h168 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1234 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1233 1 h167 kg_1217_1233
    have h169 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1235 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1234 1 h168 kg_1217_1234
    have h170 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1240 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1235 5 h169 kg_1217_1235
    have h171 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1241 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1240 1 h170 kg_1217_1240
    have h172 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1242 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1241 1 h171 kg_1217_1241
    have h173 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1244 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1242 2 h172 kg_1217_1242
    have h174 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1245 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1244 1 h173 kg_1217_1244
    have h175 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1246 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1245 1 h174 kg_1217_1245
    have h176 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1247 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1246 1 h175 kg_1217_1246
    have h177 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1248 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1247 1 h176 kg_1217_1247
    have h178 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1249 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1248 1 h177 kg_1217_1248
    have h179 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1250 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1249 1 h178 kg_1217_1249
    have h180 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1251 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1250 1 h179 kg_1217_1250
    have h181 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1269 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1251 18 h180 kg_1217_1251
    have h182 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1367 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1269 98 h181 kg_1217_1269
    have h183 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1368 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1367 1 h182 kg_1217_1367
    have h184 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1369 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1368 1 h183 kg_1217_1368
    have h185 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1383 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1369 14 h184 kg_1217_1369
    have h186 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1461 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1383 78 h185 kg_1217_1383
    have h187 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1514 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1461 53 h186 kg_1217_1461
    have h188 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1517 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1514 3 h187 kg_1217_1514
    have h189 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1531 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1517 14 h188 kg_1217_1517
    have h190 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1532 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1531 1 h189 kg_1217_1531
    have h191 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1534 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1532 2 h190 kg_1217_1532
    have h192 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1538 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1534 4 h191 kg_1217_1534
    have h193 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1543 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1538 5 h192 kg_1217_1538
    have h194 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1544 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1543 1 h193 kg_1217_1543
    have h195 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1551 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1544 7 h194 kg_1217_1544
    have h196 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1559 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1551 8 h195 kg_1217_1551
    have h197 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1564 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1559 5 h196 kg_1217_1559
    have h198 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1572 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1564 8 h197 kg_1217_1564
    have h199 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1573 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1572 1 h198 kg_1217_1572
    have h200 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1576 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1573 3 h199 kg_1217_1573
    have h201 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1577 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1576 1 h200 kg_1217_1576
    have h202 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1582 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1577 5 h201 kg_1217_1577
    have h203 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1585 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1582 3 h202 kg_1217_1582
    have h204 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1592 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1585 7 h203 kg_1217_1585
    have h205 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1595 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1592 3 h204 kg_1217_1592
    have h206 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1600 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1595 5 h205 kg_1217_1595
    have h207 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1602 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1600 2 h206 kg_1217_1600
    have h208 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1604 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1602 2 h207 kg_1217_1602
    have h209 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1610 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1604 6 h208 kg_1217_1604
    have h210 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1611 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1610 1 h209 kg_1217_1610
    have h211 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1613 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1611 2 h210 kg_1217_1611
    have h212 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1616 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1613 3 h211 kg_1217_1613
    have h213 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1621 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1616 5 h212 kg_1217_1616
    have h214 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1622 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1621 1 h213 kg_1217_1621
    have h215 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1624 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1622 2 h214 kg_1217_1622
    have h216 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1625 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1624 1 h215 kg_1217_1624
    have h217 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1627 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1625 2 h216 kg_1217_1625
    have h218 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1632 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1627 5 h217 kg_1217_1627
    have h219 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1635 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1632 3 h218 kg_1217_1632
    have h220 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1638 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1635 3 h219 kg_1217_1635
    have h221 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1641 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1638 3 h220 kg_1217_1638
    have h222 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1643 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1641 2 h221 kg_1217_1641
    have h223 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1656 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1643 13 h222 kg_1217_1643
    have h224 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1694 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1656 38 h223 kg_1217_1656
    have h225 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1712 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1694 18 h224 kg_1217_1694
    have h226 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1720 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1712 8 h225 kg_1217_1712
    have h227 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1721 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1720 1 h226 kg_1217_1720
    have h228 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1722 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1721 1 h227 kg_1217_1721
    have h229 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1723 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1722 1 h228 kg_1217_1722
    have h230 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1724 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1723 1 h229 kg_1217_1723
    have h231 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1725 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1724 1 h230 kg_1217_1724
    have h232 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1726 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1725 1 h231 kg_1217_1725
    have h233 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1727 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1726 1 h232 kg_1217_1726
    have h234 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1729 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1727 2 h233 kg_1217_1727
    have h235 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1731 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1729 2 h234 kg_1217_1729
    have h236 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1753 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1731 22 h235 kg_1217_1731
    have h237 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1760 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1753 7 h236 kg_1217_1753
    have h238 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1766 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1760 6 h237 kg_1217_1760
    have h239 : IPChk.allR (Pts.glueIB K1217.lits KW_1217) 0 1767 = true := IPChk.allR_join (Pts.glueIB K1217.lits KW_1217) 0 1766 1 h238 kg_1217_1766
    exact h239
  have hlen : K1217.lits.length = 1767 := by decide
  intro k h1 h2
  obtain rfl : k = 1217 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1217) K1217.lits KW_1217
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_249 : ∀ k, 1218 ≤ k → k < 1220 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1218 JW_1218 1218 2 jr_1218
theorem jr6_250 : ∀ k, 1220 ≤ k → k < 1221 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 359 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 2 = true := kb_1220_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 2 16 h0 kb_1220_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 18 10 h1 kb_1220_18
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 28 15 h2 kb_1220_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 43 43 h3 kb_1220_43
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 86 2 h4 kb_1220_86
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 88 15 h5 kb_1220_88
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 103 18 h6 kb_1220_103
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 121 57 h7 kb_1220_121
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 178 2 h8 kb_1220_178
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 180 14 h9 kb_1220_180
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 194 29 h10 kb_1220_194
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 223 46 h11 kb_1220_223
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 269 15 h12 kb_1220_269
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 284 17 h13 kb_1220_284
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1220.lits.getD i 0)) 0 301 58 h14 kb_1220_301
    exact h15
  have hg : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 359 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 2 = true := kg_1220_0
    have h1 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 18 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 2 16 h0 kg_1220_2
    have h2 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 28 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 18 10 h1 kg_1220_18
    have h3 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 43 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 28 15 h2 kg_1220_28
    have h4 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 86 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 43 43 h3 kg_1220_43
    have h5 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 88 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 86 2 h4 kg_1220_86
    have h6 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 103 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 88 15 h5 kg_1220_88
    have h7 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 121 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 103 18 h6 kg_1220_103
    have h8 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 178 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 121 57 h7 kg_1220_121
    have h9 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 180 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 178 2 h8 kg_1220_178
    have h10 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 194 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 180 14 h9 kg_1220_180
    have h11 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 223 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 194 29 h10 kg_1220_194
    have h12 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 269 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 223 46 h11 kg_1220_223
    have h13 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 284 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 269 15 h12 kg_1220_269
    have h14 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 301 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 284 17 h13 kg_1220_284
    have h15 : IPChk.allR (Pts.glueIB K1220.lits KW_1220) 0 359 = true := IPChk.allR_join (Pts.glueIB K1220.lits KW_1220) 0 301 58 h14 kg_1220_301
    exact h15
  have hlen : K1220.lits.length = 359 := by decide
  intro k h1 h2
  obtain rfl : k = 1220 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1220) K1220.lits KW_1220
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_251 : ∀ k, 1221 ≤ k → k < 1222 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 418 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 2 = true := kb_1221_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 2 2 h0 kb_1221_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 4 18 h1 kb_1221_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 22 4 h2 kb_1221_22
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 26 2 h3 kb_1221_26
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 28 17 h4 kb_1221_28
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 45 17 h5 kb_1221_45
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 62 13 h6 kb_1221_62
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 75 14 h7 kb_1221_75
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 89 20 h8 kb_1221_89
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 109 13 h9 kb_1221_109
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 122 5 h10 kb_1221_122
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 127 12 h11 kb_1221_127
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 139 5 h12 kb_1221_139
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 144 2 h13 kb_1221_144
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 146 12 h14 kb_1221_146
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 158 2 h15 kb_1221_158
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 160 12 h16 kb_1221_160
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 172 12 h17 kb_1221_172
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 184 15 h18 kb_1221_184
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 199 51 h19 kb_1221_199
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 250 10 h20 kb_1221_250
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 260 2 h21 kb_1221_260
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 262 13 h22 kb_1221_262
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 275 6 h23 kb_1221_275
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 281 13 h24 kb_1221_281
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 294 5 h25 kb_1221_294
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 299 21 h26 kb_1221_299
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 320 13 h27 kb_1221_320
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 333 4 h28 kb_1221_333
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 349 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 337 12 h29 kb_1221_337
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 349 3 h30 kb_1221_349
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 352 31 h31 kb_1221_352
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 0 383 35 h32 kb_1221_383
    exact h33
  have hg : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 418 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 2 = true := kg_1221_0
    have h1 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 4 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 2 2 h0 kg_1221_2
    have h2 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 22 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 4 18 h1 kg_1221_4
    have h3 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 26 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 22 4 h2 kg_1221_22
    have h4 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 28 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 26 2 h3 kg_1221_26
    have h5 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 45 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 28 17 h4 kg_1221_28
    have h6 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 62 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 45 17 h5 kg_1221_45
    have h7 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 75 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 62 13 h6 kg_1221_62
    have h8 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 89 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 75 14 h7 kg_1221_75
    have h9 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 109 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 89 20 h8 kg_1221_89
    have h10 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 122 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 109 13 h9 kg_1221_109
    have h11 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 127 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 122 5 h10 kg_1221_122
    have h12 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 139 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 127 12 h11 kg_1221_127
    have h13 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 144 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 139 5 h12 kg_1221_139
    have h14 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 146 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 144 2 h13 kg_1221_144
    have h15 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 158 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 146 12 h14 kg_1221_146
    have h16 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 160 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 158 2 h15 kg_1221_158
    have h17 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 172 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 160 12 h16 kg_1221_160
    have h18 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 184 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 172 12 h17 kg_1221_172
    have h19 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 199 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 184 15 h18 kg_1221_184
    have h20 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 250 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 199 51 h19 kg_1221_199
    have h21 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 260 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 250 10 h20 kg_1221_250
    have h22 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 262 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 260 2 h21 kg_1221_260
    have h23 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 275 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 262 13 h22 kg_1221_262
    have h24 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 281 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 275 6 h23 kg_1221_275
    have h25 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 294 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 281 13 h24 kg_1221_281
    have h26 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 299 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 294 5 h25 kg_1221_294
    have h27 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 320 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 299 21 h26 kg_1221_299
    have h28 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 333 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 320 13 h27 kg_1221_320
    have h29 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 337 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 333 4 h28 kg_1221_333
    have h30 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 349 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 337 12 h29 kg_1221_337
    have h31 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 352 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 349 3 h30 kg_1221_349
    have h32 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 383 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 352 31 h31 kg_1221_352
    have h33 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 0 418 = true := IPChk.allR_join (Pts.glueIB K1221.lits KW_1221) 0 383 35 h32 kg_1221_383
    exact h33
  have hlen : K1221.lits.length = 418 := by decide
  intro k h1 h2
  obtain rfl : k = 1221 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1221) K1221.lits KW_1221
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_252 : ∀ k, 1222 ≤ k → k < 1227 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1222 JW_1222 1222 5 jr_1222
theorem jr6_253 : ∀ k, 1227 ≤ k → k < 1228 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 57 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 2 = true := kb_1227_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 2 4 h0 kb_1227_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 6 2 h1 kb_1227_6
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 8 12 h2 kb_1227_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 20 26 h3 kb_1227_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 46 7 h4 kb_1227_46
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 53 1 h5 kb_1227_53
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 54 1 h6 kb_1227_54
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1227.lits.getD i 0)) 0 55 2 h7 kb_1227_55
    exact h8
  have hg : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 57 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 2 = true := kg_1227_0
    have h1 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 6 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 2 4 h0 kg_1227_2
    have h2 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 8 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 6 2 h1 kg_1227_6
    have h3 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 20 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 8 12 h2 kg_1227_8
    have h4 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 46 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 20 26 h3 kg_1227_20
    have h5 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 53 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 46 7 h4 kg_1227_46
    have h6 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 54 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 53 1 h5 kg_1227_53
    have h7 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 55 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 54 1 h6 kg_1227_54
    have h8 : IPChk.allR (Pts.glueIB K1227.lits KW_1227) 0 57 = true := IPChk.allR_join (Pts.glueIB K1227.lits KW_1227) 0 55 2 h7 kg_1227_55
    exact h8
  have hlen : K1227.lits.length = 57 := by decide
  intro k h1 h2
  obtain rfl : k = 1227 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1227) K1227.lits KW_1227
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_254 : ∀ k, 1228 ≤ k → k < 1248 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1228 JW_1228 1228 20 jr_1228
theorem jr6_255 : ∀ k, 1248 ≤ k → k < 1249 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1248.lits.getD i 0)) 0 2 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1248.lits.getD i 0)) 0 1 = true := kb_1248_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1248.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1248.lits.getD i 0)) 0 1 1 h0 kb_1248_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K1248.lits KW_1248) 0 2 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1248.lits KW_1248) 0 1 = true := kg_1248_0
    have h1 : IPChk.allR (Pts.glueIB K1248.lits KW_1248) 0 2 = true := IPChk.allR_join (Pts.glueIB K1248.lits KW_1248) 0 1 1 h0 kg_1248_1
    exact h1
  have hlen : K1248.lits.length = 2 := by decide
  intro k h1 h2
  obtain rfl : k = 1248 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1248) K1248.lits KW_1248
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_256 : ∀ k, 1249 ≤ k → k < 1250 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1249.lits.getD i 0)) 0 4 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1249.lits.getD i 0)) 0 2 = true := kb_1249_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1249.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1249.lits.getD i 0)) 0 2 2 h0 kb_1249_2
    exact h1
  have hg : IPChk.allR (Pts.glueIB K1249.lits KW_1249) 0 4 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1249.lits KW_1249) 0 2 = true := kg_1249_0
    have h1 : IPChk.allR (Pts.glueIB K1249.lits KW_1249) 0 4 = true := IPChk.allR_join (Pts.glueIB K1249.lits KW_1249) 0 2 2 h0 kg_1249_2
    exact h1
  have hlen : K1249.lits.length = 4 := by decide
  intro k h1 h2
  obtain rfl : k = 1249 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1249) K1249.lits KW_1249
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_257 : ∀ k, 1250 ≤ k → k < 1251 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1250 JW_1250 1250 1 jr_1250
theorem jr6_258 : ∀ k, 1251 ≤ k → k < 1252 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1250 JW_1250 1251 1 jr_1251

theorem grp6_8 : ∀ k, 1215 ≤ k → k < 1252 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_246
  have a1 := Pts.fa_join a0 jr6_247
  have a2 := Pts.fa_join a1 jr6_248
  have a3 := Pts.fa_join a2 jr6_249
  have a4 := Pts.fa_join a3 jr6_250
  have a5 := Pts.fa_join a4 jr6_251
  have a6 := Pts.fa_join a5 jr6_252
  have a7 := Pts.fa_join a6 jr6_253
  have a8 := Pts.fa_join a7 jr6_254
  have a9 := Pts.fa_join a8 jr6_255
  have a10 := Pts.fa_join a9 jr6_256
  have a11 := Pts.fa_join a10 jr6_257
  have a12 := Pts.fa_join a11 jr6_258
  exact a12

end B334.E1x.Pts.S707
