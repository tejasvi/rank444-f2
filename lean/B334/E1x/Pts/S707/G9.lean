import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J1253
import B334.E1x.Pts.S707.J1255
import B334.E1x.Pts.S707.J1258
import B334.E1x.Pts.S707.J1260
import B334.E1x.Pts.S707.J1266
import B334.E1x.Pts.S707.J1283
import B334.E1x.Pts.S707.J1345
import B334.E1x.Pts.S707.K1252L
import B334.E1x.Pts.S707.K1254L
import B334.E1x.Pts.S707.K1257L
import B334.E1x.Pts.S707.K1259L
import B334.E1x.Pts.S707.K1265L
import B334.E1x.Pts.S707.K1282L
import B334.E1x.Pts.S707.K1344L
import B334.E1x.Pts.S707.K1252Q0
import B334.E1x.Pts.S707.K1252Q1
import B334.E1x.Pts.S707.K1252Q2
import B334.E1x.Pts.S707.K1252Q3
import B334.E1x.Pts.S707.K1252Q4
import B334.E1x.Pts.S707.K1252Q5
import B334.E1x.Pts.S707.K1252Q6
import B334.E1x.Pts.S707.K1252Q7
import B334.E1x.Pts.S707.K1252Q8
import B334.E1x.Pts.S707.K1252Q9
import B334.E1x.Pts.S707.K1254Q0
import B334.E1x.Pts.S707.K1254Q1
import B334.E1x.Pts.S707.K1254Q2
import B334.E1x.Pts.S707.K1254Q3
import B334.E1x.Pts.S707.K1254Q4
import B334.E1x.Pts.S707.K1254Q5
import B334.E1x.Pts.S707.K1254Q6
import B334.E1x.Pts.S707.K1254Q7
import B334.E1x.Pts.S707.K1254Q8
import B334.E1x.Pts.S707.K1254Q9
import B334.E1x.Pts.S707.K1257Q0
import B334.E1x.Pts.S707.K1257Q1
import B334.E1x.Pts.S707.K1257Q2
import B334.E1x.Pts.S707.K1257Q3
import B334.E1x.Pts.S707.K1257Q4
import B334.E1x.Pts.S707.K1257Q5
import B334.E1x.Pts.S707.K1257Q6
import B334.E1x.Pts.S707.K1257Q7
import B334.E1x.Pts.S707.K1257Q8
import B334.E1x.Pts.S707.K1257Q9
import B334.E1x.Pts.S707.K1259Q0
import B334.E1x.Pts.S707.K1259Q1
import B334.E1x.Pts.S707.K1259Q2
import B334.E1x.Pts.S707.K1259Q3
import B334.E1x.Pts.S707.K1259Q4
import B334.E1x.Pts.S707.K1259Q5
import B334.E1x.Pts.S707.K1265Q0
import B334.E1x.Pts.S707.K1265Q1
import B334.E1x.Pts.S707.K1265Q2
import B334.E1x.Pts.S707.K1282Q0
import B334.E1x.Pts.S707.K1344Q0
import B334.E1x.Pts.S707.K1344Q1
import B334.E1x.Pts.S707.K1344Q2
import B334.E1x.Pts.S707.K1344Q3
import B334.E1x.Pts.S707.K1344Q4
import B334.E1x.Pts.S707.K1344Q5
import B334.E1x.Pts.S707.K1252Q10
import B334.E1x.Pts.S707.K1252Q11
import B334.E1x.Pts.S707.K1252Q12
import B334.E1x.Pts.S707.K1252Q13
import B334.E1x.Pts.S707.K1252Q14
import B334.E1x.Pts.S707.K1252Q15
import B334.E1x.Pts.S707.K1252Q16
import B334.E1x.Pts.S707.K1252Q17
import B334.E1x.Pts.S707.K1252Q18
import B334.E1x.Pts.S707.K1252Q19
import B334.E1x.Pts.S707.K1252Q20
import B334.E1x.Pts.S707.K1254Q10
import B334.E1x.Pts.S707.K1254Q11
import B334.E1x.Pts.S707.K1254Q12
import B334.E1x.Pts.S707.K1257Q10
import B334.E1x.Pts.S707.K1257Q11

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 1252 … 1346 (stage707_v6): the v5 Fin's job blocks r259 … r277 as
theorems, joined into `grp6_9` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_259 : ∀ k, 1252 ≤ k → k < 1253 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1419 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 4 = true := kb_1252_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 4 3 h0 kb_1252_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 7 7 h1 kb_1252_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 14 9 h2 kb_1252_14
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 23 7 h3 kb_1252_23
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 30 8 h4 kb_1252_30
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 38 10 h5 kb_1252_38
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 48 9 h6 kb_1252_48
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 57 1 h7 kb_1252_57
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 58 1 h8 kb_1252_58
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 59 8 h9 kb_1252_59
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 67 21 h10 kb_1252_67
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 88 2 h11 kb_1252_88
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 90 7 h12 kb_1252_90
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 97 12 h13 kb_1252_97
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 109 11 h14 kb_1252_109
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 120 1 h15 kb_1252_120
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 121 1 h16 kb_1252_121
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 122 10 h17 kb_1252_122
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 132 8 h18 kb_1252_132
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 140 3 h19 kb_1252_140
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 143 1 h20 kb_1252_143
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 144 9 h21 kb_1252_144
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 153 2 h22 kb_1252_153
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 155 7 h23 kb_1252_155
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 162 18 h24 kb_1252_162
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 180 3 h25 kb_1252_180
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 183 13 h26 kb_1252_183
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 196 13 h27 kb_1252_196
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 209 2 h28 kb_1252_209
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 211 6 h29 kb_1252_211
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 217 2 h30 kb_1252_217
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 219 23 h31 kb_1252_219
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 242 8 h32 kb_1252_242
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 250 22 h33 kb_1252_250
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 272 1 h34 kb_1252_272
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 273 2 h35 kb_1252_273
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 275 2 h36 kb_1252_275
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 277 3 h37 kb_1252_277
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 280 2 h38 kb_1252_280
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 282 29 h39 kb_1252_282
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 311 2 h40 kb_1252_311
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 313 7 h41 kb_1252_313
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 320 22 h42 kb_1252_320
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 342 1 h43 kb_1252_342
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 343 11 h44 kb_1252_343
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 354 4 h45 kb_1252_354
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 358 12 h46 kb_1252_358
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 370 12 h47 kb_1252_370
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 382 2 h48 kb_1252_382
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 384 12 h49 kb_1252_384
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 396 12 h50 kb_1252_396
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 408 2 h51 kb_1252_408
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 410 12 h52 kb_1252_410
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 422 2 h53 kb_1252_422
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 424 1 h54 kb_1252_424
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 425 2 h55 kb_1252_425
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 427 1 h56 kb_1252_427
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 428 3 h57 kb_1252_428
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 431 2 h58 kb_1252_431
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 433 1 h59 kb_1252_433
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 435 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 434 1 h60 kb_1252_434
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 435 1 h61 kb_1252_435
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 436 2 h62 kb_1252_436
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 438 1 h63 kb_1252_438
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 440 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 439 1 h64 kb_1252_439
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 440 2 h65 kb_1252_440
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 442 1 h66 kb_1252_442
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 443 1 h67 kb_1252_443
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 444 2 h68 kb_1252_444
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 446 1 h69 kb_1252_446
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 447 2 h70 kb_1252_447
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 449 1 h71 kb_1252_449
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 450 1 h72 kb_1252_450
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 451 2 h73 kb_1252_451
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 453 4 h74 kb_1252_453
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 457 12 h75 kb_1252_457
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 469 5 h76 kb_1252_469
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 475 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 474 1 h77 kb_1252_474
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 475 6 h78 kb_1252_475
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 481 4 h79 kb_1252_481
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 485 19 h80 kb_1252_485
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 504 2 h81 kb_1252_504
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 526 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 506 20 h82 kb_1252_506
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 528 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 526 2 h83 kb_1252_526
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 528 12 h84 kb_1252_528
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 540 6 h85 kb_1252_540
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 546 2 h86 kb_1252_546
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 548 18 h87 kb_1252_548
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 571 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 566 5 h88 kb_1252_566
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 577 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 571 6 h89 kb_1252_571
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 577 2 h90 kb_1252_577
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 598 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 579 19 h91 kb_1252_579
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 598 2 h92 kb_1252_598
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 600 22 h93 kb_1252_600
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 622 2 h94 kb_1252_622
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 624 12 h95 kb_1252_624
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 647 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 636 11 h96 kb_1252_636
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 651 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 647 4 h97 kb_1252_647
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 651 10 h98 kb_1252_651
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 661 7 h99 kb_1252_661
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 668 7 h100 kb_1252_668
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 675 1 h101 kb_1252_675
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 676 1 h102 kb_1252_676
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 677 1 h103 kb_1252_677
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 678 4 h104 kb_1252_678
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 694 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 682 12 h105 kb_1252_682
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 694 23 h106 kb_1252_694
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 717 2 h107 kb_1252_717
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 719 20 h108 kb_1252_719
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 744 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 739 5 h109 kb_1252_739
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 755 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 744 11 h110 kb_1252_744
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 755 1 h111 kb_1252_755
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 776 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 756 20 h112 kb_1252_756
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 788 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 776 12 h113 kb_1252_776
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 788 6 h114 kb_1252_788
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 794 2 h115 kb_1252_794
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 796 22 h116 kb_1252_796
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 818 9 h117 kb_1252_818
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 882 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 827 55 h118 kb_1252_827
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 882 4 h119 kb_1252_882
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 887 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 886 1 h120 kb_1252_886
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 909 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 887 22 h121 kb_1252_887
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 911 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 909 2 h122 kb_1252_909
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 911 21 h123 kb_1252_911
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 933 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 932 1 h124 kb_1252_932
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 941 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 933 8 h125 kb_1252_933
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 941 8 h126 kb_1252_941
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 950 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 949 1 h127 kb_1252_949
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 959 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 950 9 h128 kb_1252_950
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 961 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 959 2 h129 kb_1252_959
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 969 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 961 8 h130 kb_1252_961
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 980 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 969 11 h131 kb_1252_969
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 981 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 980 1 h132 kb_1252_980
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 987 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 981 6 h133 kb_1252_981
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 987 2 h134 kb_1252_987
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 990 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 989 1 h135 kb_1252_989
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 990 1 h136 kb_1252_990
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 992 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 991 1 h137 kb_1252_991
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 993 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 992 1 h138 kb_1252_992
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 995 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 993 2 h139 kb_1252_993
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 995 1 h140 kb_1252_995
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 998 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 996 2 h141 kb_1252_996
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1000 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 998 2 h142 kb_1252_998
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1001 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1000 1 h143 kb_1252_1000
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1002 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1001 1 h144 kb_1252_1001
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1003 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1002 1 h145 kb_1252_1002
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1003 2 h146 kb_1252_1003
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1008 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1005 3 h147 kb_1252_1005
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1016 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1008 8 h148 kb_1252_1008
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1024 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1016 8 h149 kb_1252_1016
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1026 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1024 2 h150 kb_1252_1024
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1027 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1026 1 h151 kb_1252_1026
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1027 1 h152 kb_1252_1027
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1047 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1028 19 h153 kb_1252_1028
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1050 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1047 3 h154 kb_1252_1047
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1051 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1050 1 h155 kb_1252_1050
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1051 18 h156 kb_1252_1051
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1069 2 h157 kb_1252_1069
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1087 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1071 16 h158 kb_1252_1071
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1095 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1087 8 h159 kb_1252_1087
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1095 11 h160 kb_1252_1095
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1106 6 h161 kb_1252_1106
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1112 5 h162 kb_1252_1112
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1117 8 h163 kb_1252_1117
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1125 7 h164 kb_1252_1125
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1132 2 h165 kb_1252_1132
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1134 11 h166 kb_1252_1134
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1145 3 h167 kb_1252_1145
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1148 4 h168 kb_1252_1148
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1152 23 h169 kb_1252_1152
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1175 3 h170 kb_1252_1175
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1178 2 h171 kb_1252_1178
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1180 13 h172 kb_1252_1180
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1193 2 h173 kb_1252_1193
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1195 3 h174 kb_1252_1195
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1198 15 h175 kb_1252_1198
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1213 4 h176 kb_1252_1213
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1217 8 h177 kb_1252_1217
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1225 2 h178 kb_1252_1225
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1227 3 h179 kb_1252_1227
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1230 2 h180 kb_1252_1230
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1232 3 h181 kb_1252_1232
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1235 2 h182 kb_1252_1235
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1237 13 h183 kb_1252_1237
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1250 2 h184 kb_1252_1250
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1252 1 h185 kb_1252_1252
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1253 1 h186 kb_1252_1253
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1254 20 h187 kb_1252_1254
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1274 1 h188 kb_1252_1274
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1275 17 h189 kb_1252_1275
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1292 5 h190 kb_1252_1292
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1297 15 h191 kb_1252_1297
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1312 22 h192 kb_1252_1312
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1334 6 h193 kb_1252_1334
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1340 3 h194 kb_1252_1340
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1343 4 h195 kb_1252_1343
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1347 3 h196 kb_1252_1347
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1350 2 h197 kb_1252_1350
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1352 11 h198 kb_1252_1352
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1363 2 h199 kb_1252_1363
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1365 2 h200 kb_1252_1365
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1367 3 h201 kb_1252_1367
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1370 2 h202 kb_1252_1370
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1372 3 h203 kb_1252_1372
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1375 3 h204 kb_1252_1375
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1378 3 h205 kb_1252_1378
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1381 3 h206 kb_1252_1381
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1384 4 h207 kb_1252_1384
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1388 18 h208 kb_1252_1388
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1406 5 h209 kb_1252_1406
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 0 1411 8 h210 kb_1252_1411
    exact h211
  have hg : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1419 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 4 = true := kg_1252_0
    have h1 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 7 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 4 3 h0 kg_1252_4
    have h2 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 14 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 7 7 h1 kg_1252_7
    have h3 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 23 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 14 9 h2 kg_1252_14
    have h4 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 30 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 23 7 h3 kg_1252_23
    have h5 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 38 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 30 8 h4 kg_1252_30
    have h6 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 48 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 38 10 h5 kg_1252_38
    have h7 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 57 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 48 9 h6 kg_1252_48
    have h8 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 58 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 57 1 h7 kg_1252_57
    have h9 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 59 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 58 1 h8 kg_1252_58
    have h10 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 67 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 59 8 h9 kg_1252_59
    have h11 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 88 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 67 21 h10 kg_1252_67
    have h12 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 90 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 88 2 h11 kg_1252_88
    have h13 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 97 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 90 7 h12 kg_1252_90
    have h14 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 109 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 97 12 h13 kg_1252_97
    have h15 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 120 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 109 11 h14 kg_1252_109
    have h16 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 121 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 120 1 h15 kg_1252_120
    have h17 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 122 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 121 1 h16 kg_1252_121
    have h18 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 132 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 122 10 h17 kg_1252_122
    have h19 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 140 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 132 8 h18 kg_1252_132
    have h20 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 143 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 140 3 h19 kg_1252_140
    have h21 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 144 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 143 1 h20 kg_1252_143
    have h22 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 153 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 144 9 h21 kg_1252_144
    have h23 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 155 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 153 2 h22 kg_1252_153
    have h24 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 162 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 155 7 h23 kg_1252_155
    have h25 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 180 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 162 18 h24 kg_1252_162
    have h26 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 183 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 180 3 h25 kg_1252_180
    have h27 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 196 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 183 13 h26 kg_1252_183
    have h28 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 209 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 196 13 h27 kg_1252_196
    have h29 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 211 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 209 2 h28 kg_1252_209
    have h30 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 217 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 211 6 h29 kg_1252_211
    have h31 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 219 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 217 2 h30 kg_1252_217
    have h32 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 242 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 219 23 h31 kg_1252_219
    have h33 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 250 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 242 8 h32 kg_1252_242
    have h34 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 272 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 250 22 h33 kg_1252_250
    have h35 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 273 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 272 1 h34 kg_1252_272
    have h36 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 275 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 273 2 h35 kg_1252_273
    have h37 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 277 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 275 2 h36 kg_1252_275
    have h38 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 280 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 277 3 h37 kg_1252_277
    have h39 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 282 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 280 2 h38 kg_1252_280
    have h40 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 311 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 282 29 h39 kg_1252_282
    have h41 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 313 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 311 2 h40 kg_1252_311
    have h42 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 320 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 313 7 h41 kg_1252_313
    have h43 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 342 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 320 22 h42 kg_1252_320
    have h44 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 343 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 342 1 h43 kg_1252_342
    have h45 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 354 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 343 11 h44 kg_1252_343
    have h46 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 358 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 354 4 h45 kg_1252_354
    have h47 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 370 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 358 12 h46 kg_1252_358
    have h48 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 382 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 370 12 h47 kg_1252_370
    have h49 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 384 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 382 2 h48 kg_1252_382
    have h50 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 396 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 384 12 h49 kg_1252_384
    have h51 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 408 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 396 12 h50 kg_1252_396
    have h52 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 410 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 408 2 h51 kg_1252_408
    have h53 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 422 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 410 12 h52 kg_1252_410
    have h54 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 424 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 422 2 h53 kg_1252_422
    have h55 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 425 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 424 1 h54 kg_1252_424
    have h56 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 427 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 425 2 h55 kg_1252_425
    have h57 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 428 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 427 1 h56 kg_1252_427
    have h58 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 431 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 428 3 h57 kg_1252_428
    have h59 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 433 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 431 2 h58 kg_1252_431
    have h60 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 434 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 433 1 h59 kg_1252_433
    have h61 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 435 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 434 1 h60 kg_1252_434
    have h62 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 436 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 435 1 h61 kg_1252_435
    have h63 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 438 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 436 2 h62 kg_1252_436
    have h64 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 439 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 438 1 h63 kg_1252_438
    have h65 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 440 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 439 1 h64 kg_1252_439
    have h66 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 442 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 440 2 h65 kg_1252_440
    have h67 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 443 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 442 1 h66 kg_1252_442
    have h68 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 444 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 443 1 h67 kg_1252_443
    have h69 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 446 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 444 2 h68 kg_1252_444
    have h70 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 447 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 446 1 h69 kg_1252_446
    have h71 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 449 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 447 2 h70 kg_1252_447
    have h72 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 450 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 449 1 h71 kg_1252_449
    have h73 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 451 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 450 1 h72 kg_1252_450
    have h74 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 453 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 451 2 h73 kg_1252_451
    have h75 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 457 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 453 4 h74 kg_1252_453
    have h76 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 469 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 457 12 h75 kg_1252_457
    have h77 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 474 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 469 5 h76 kg_1252_469
    have h78 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 475 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 474 1 h77 kg_1252_474
    have h79 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 481 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 475 6 h78 kg_1252_475
    have h80 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 485 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 481 4 h79 kg_1252_481
    have h81 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 504 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 485 19 h80 kg_1252_485
    have h82 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 506 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 504 2 h81 kg_1252_504
    have h83 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 526 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 506 20 h82 kg_1252_506
    have h84 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 528 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 526 2 h83 kg_1252_526
    have h85 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 540 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 528 12 h84 kg_1252_528
    have h86 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 546 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 540 6 h85 kg_1252_540
    have h87 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 548 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 546 2 h86 kg_1252_546
    have h88 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 566 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 548 18 h87 kg_1252_548
    have h89 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 571 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 566 5 h88 kg_1252_566
    have h90 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 577 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 571 6 h89 kg_1252_571
    have h91 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 579 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 577 2 h90 kg_1252_577
    have h92 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 598 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 579 19 h91 kg_1252_579
    have h93 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 600 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 598 2 h92 kg_1252_598
    have h94 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 622 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 600 22 h93 kg_1252_600
    have h95 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 624 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 622 2 h94 kg_1252_622
    have h96 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 636 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 624 12 h95 kg_1252_624
    have h97 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 647 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 636 11 h96 kg_1252_636
    have h98 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 651 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 647 4 h97 kg_1252_647
    have h99 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 661 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 651 10 h98 kg_1252_651
    have h100 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 668 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 661 7 h99 kg_1252_661
    have h101 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 675 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 668 7 h100 kg_1252_668
    have h102 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 676 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 675 1 h101 kg_1252_675
    have h103 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 677 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 676 1 h102 kg_1252_676
    have h104 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 678 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 677 1 h103 kg_1252_677
    have h105 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 682 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 678 4 h104 kg_1252_678
    have h106 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 694 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 682 12 h105 kg_1252_682
    have h107 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 717 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 694 23 h106 kg_1252_694
    have h108 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 719 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 717 2 h107 kg_1252_717
    have h109 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 739 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 719 20 h108 kg_1252_719
    have h110 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 744 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 739 5 h109 kg_1252_739
    have h111 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 755 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 744 11 h110 kg_1252_744
    have h112 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 756 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 755 1 h111 kg_1252_755
    have h113 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 776 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 756 20 h112 kg_1252_756
    have h114 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 788 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 776 12 h113 kg_1252_776
    have h115 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 794 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 788 6 h114 kg_1252_788
    have h116 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 796 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 794 2 h115 kg_1252_794
    have h117 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 818 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 796 22 h116 kg_1252_796
    have h118 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 827 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 818 9 h117 kg_1252_818
    have h119 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 882 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 827 55 h118 kg_1252_827
    have h120 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 886 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 882 4 h119 kg_1252_882
    have h121 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 887 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 886 1 h120 kg_1252_886
    have h122 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 909 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 887 22 h121 kg_1252_887
    have h123 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 911 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 909 2 h122 kg_1252_909
    have h124 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 932 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 911 21 h123 kg_1252_911
    have h125 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 933 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 932 1 h124 kg_1252_932
    have h126 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 941 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 933 8 h125 kg_1252_933
    have h127 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 949 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 941 8 h126 kg_1252_941
    have h128 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 950 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 949 1 h127 kg_1252_949
    have h129 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 959 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 950 9 h128 kg_1252_950
    have h130 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 961 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 959 2 h129 kg_1252_959
    have h131 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 969 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 961 8 h130 kg_1252_961
    have h132 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 980 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 969 11 h131 kg_1252_969
    have h133 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 981 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 980 1 h132 kg_1252_980
    have h134 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 987 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 981 6 h133 kg_1252_981
    have h135 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 989 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 987 2 h134 kg_1252_987
    have h136 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 990 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 989 1 h135 kg_1252_989
    have h137 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 991 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 990 1 h136 kg_1252_990
    have h138 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 992 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 991 1 h137 kg_1252_991
    have h139 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 993 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 992 1 h138 kg_1252_992
    have h140 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 995 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 993 2 h139 kg_1252_993
    have h141 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 996 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 995 1 h140 kg_1252_995
    have h142 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 998 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 996 2 h141 kg_1252_996
    have h143 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1000 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 998 2 h142 kg_1252_998
    have h144 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1001 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1000 1 h143 kg_1252_1000
    have h145 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1002 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1001 1 h144 kg_1252_1001
    have h146 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1003 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1002 1 h145 kg_1252_1002
    have h147 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1005 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1003 2 h146 kg_1252_1003
    have h148 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1008 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1005 3 h147 kg_1252_1005
    have h149 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1016 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1008 8 h148 kg_1252_1008
    have h150 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1024 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1016 8 h149 kg_1252_1016
    have h151 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1026 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1024 2 h150 kg_1252_1024
    have h152 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1027 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1026 1 h151 kg_1252_1026
    have h153 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1028 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1027 1 h152 kg_1252_1027
    have h154 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1047 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1028 19 h153 kg_1252_1028
    have h155 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1050 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1047 3 h154 kg_1252_1047
    have h156 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1051 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1050 1 h155 kg_1252_1050
    have h157 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1069 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1051 18 h156 kg_1252_1051
    have h158 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1071 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1069 2 h157 kg_1252_1069
    have h159 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1087 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1071 16 h158 kg_1252_1071
    have h160 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1095 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1087 8 h159 kg_1252_1087
    have h161 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1106 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1095 11 h160 kg_1252_1095
    have h162 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1112 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1106 6 h161 kg_1252_1106
    have h163 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1117 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1112 5 h162 kg_1252_1112
    have h164 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1125 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1117 8 h163 kg_1252_1117
    have h165 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1132 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1125 7 h164 kg_1252_1125
    have h166 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1134 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1132 2 h165 kg_1252_1132
    have h167 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1145 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1134 11 h166 kg_1252_1134
    have h168 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1148 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1145 3 h167 kg_1252_1145
    have h169 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1152 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1148 4 h168 kg_1252_1148
    have h170 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1175 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1152 23 h169 kg_1252_1152
    have h171 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1178 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1175 3 h170 kg_1252_1175
    have h172 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1180 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1178 2 h171 kg_1252_1178
    have h173 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1193 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1180 13 h172 kg_1252_1180
    have h174 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1195 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1193 2 h173 kg_1252_1193
    have h175 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1198 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1195 3 h174 kg_1252_1195
    have h176 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1213 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1198 15 h175 kg_1252_1198
    have h177 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1217 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1213 4 h176 kg_1252_1213
    have h178 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1225 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1217 8 h177 kg_1252_1217
    have h179 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1227 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1225 2 h178 kg_1252_1225
    have h180 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1230 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1227 3 h179 kg_1252_1227
    have h181 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1232 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1230 2 h180 kg_1252_1230
    have h182 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1235 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1232 3 h181 kg_1252_1232
    have h183 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1237 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1235 2 h182 kg_1252_1235
    have h184 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1250 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1237 13 h183 kg_1252_1237
    have h185 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1252 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1250 2 h184 kg_1252_1250
    have h186 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1253 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1252 1 h185 kg_1252_1252
    have h187 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1254 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1253 1 h186 kg_1252_1253
    have h188 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1274 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1254 20 h187 kg_1252_1254
    have h189 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1275 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1274 1 h188 kg_1252_1274
    have h190 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1292 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1275 17 h189 kg_1252_1275
    have h191 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1297 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1292 5 h190 kg_1252_1292
    have h192 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1312 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1297 15 h191 kg_1252_1297
    have h193 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1334 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1312 22 h192 kg_1252_1312
    have h194 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1340 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1334 6 h193 kg_1252_1334
    have h195 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1343 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1340 3 h194 kg_1252_1340
    have h196 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1347 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1343 4 h195 kg_1252_1343
    have h197 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1350 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1347 3 h196 kg_1252_1347
    have h198 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1352 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1350 2 h197 kg_1252_1350
    have h199 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1363 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1352 11 h198 kg_1252_1352
    have h200 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1365 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1363 2 h199 kg_1252_1363
    have h201 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1367 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1365 2 h200 kg_1252_1365
    have h202 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1370 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1367 3 h201 kg_1252_1367
    have h203 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1372 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1370 2 h202 kg_1252_1370
    have h204 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1375 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1372 3 h203 kg_1252_1372
    have h205 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1378 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1375 3 h204 kg_1252_1375
    have h206 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1381 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1378 3 h205 kg_1252_1378
    have h207 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1384 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1381 3 h206 kg_1252_1381
    have h208 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1388 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1384 4 h207 kg_1252_1384
    have h209 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1406 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1388 18 h208 kg_1252_1388
    have h210 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1411 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1406 5 h209 kg_1252_1406
    have h211 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 0 1419 = true := IPChk.allR_join (Pts.glueIB K1252.lits KW_1252) 0 1411 8 h210 kg_1252_1411
    exact h211
  have hlen : K1252.lits.length = 1419 := by decide
  intro k h1 h2
  obtain rfl : k = 1252 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1252) K1252.lits KW_1252
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_260 : ∀ k, 1253 ≤ k → k < 1254 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1253 JW_1253 1253 1 jr_1253
theorem jr6_261 : ∀ k, 1254 ≤ k → k < 1255 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1455 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 5 = true := kb_1254_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 5 8 h0 kb_1254_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 13 8 h1 kb_1254_13
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 21 6 h2 kb_1254_21
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 27 8 h3 kb_1254_27
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 35 14 h4 kb_1254_35
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 49 1 h5 kb_1254_49
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 50 11 h6 kb_1254_50
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 61 21 h7 kb_1254_61
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 82 6 h8 kb_1254_82
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 88 2 h9 kb_1254_88
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 90 21 h10 kb_1254_90
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 111 3 h11 kb_1254_111
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 114 7 h12 kb_1254_114
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 121 7 h13 kb_1254_121
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 128 23 h14 kb_1254_128
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 151 1 h15 kb_1254_151
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 152 5 h16 kb_1254_152
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 157 1 h17 kb_1254_157
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 158 2 h18 kb_1254_158
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 160 2 h19 kb_1254_160
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 162 11 h20 kb_1254_162
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 173 20 h21 kb_1254_173
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 193 8 h22 kb_1254_193
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 201 20 h23 kb_1254_201
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 221 2 h24 kb_1254_221
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 223 12 h25 kb_1254_223
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 235 19 h26 kb_1254_235
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 254 6 h27 kb_1254_254
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 260 2 h28 kb_1254_260
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 262 22 h29 kb_1254_262
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 287 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 284 3 h30 kb_1254_284
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 287 1 h31 kb_1254_287
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 288 11 h32 kb_1254_288
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 299 4 h33 kb_1254_299
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 303 12 h34 kb_1254_303
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 315 12 h35 kb_1254_315
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 327 2 h36 kb_1254_327
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 329 12 h37 kb_1254_329
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 341 12 h38 kb_1254_341
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 353 14 h39 kb_1254_353
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 367 6 h40 kb_1254_367
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 373 2 h41 kb_1254_373
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 397 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 375 22 h42 kb_1254_375
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 397 2 h43 kb_1254_397
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 399 8 h44 kb_1254_399
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 407 2 h45 kb_1254_407
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 409 21 h46 kb_1254_409
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 430 4 h47 kb_1254_430
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 456 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 434 22 h48 kb_1254_434
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 456 1 h49 kb_1254_456
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 457 22 h50 kb_1254_457
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 479 1 h51 kb_1254_479
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 480 2 h52 kb_1254_480
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 482 3 h53 kb_1254_482
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 485 10 h54 kb_1254_485
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 495 9 h55 kb_1254_495
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 512 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 504 8 h56 kb_1254_504
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 512 2 h57 kb_1254_512
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 514 1 h58 kb_1254_514
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 515 15 h59 kb_1254_515
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 530 20 h60 kb_1254_530
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 550 3 h61 kb_1254_550
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 571 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 553 18 h62 kb_1254_553
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 571 9 h63 kb_1254_571
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 580 4 h64 kb_1254_580
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 595 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 584 11 h65 kb_1254_584
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 595 12 h66 kb_1254_595
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 607 11 h67 kb_1254_607
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 618 4 h68 kb_1254_618
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 622 12 h69 kb_1254_622
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 645 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 634 11 h70 kb_1254_634
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 647 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 645 2 h71 kb_1254_645
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 647 11 h72 kb_1254_647
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 658 6 h73 kb_1254_658
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 664 2 h74 kb_1254_664
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 666 21 h75 kb_1254_666
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 687 8 h76 kb_1254_687
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 695 2 h77 kb_1254_695
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 697 19 h78 kb_1254_697
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 748 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 716 32 h79 kb_1254_716
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 748 33 h80 kb_1254_748
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 781 2 h81 kb_1254_781
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 783 6 h82 kb_1254_783
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 801 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 789 12 h83 kb_1254_789
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 870 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 801 69 h84 kb_1254_801
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 870 7 h85 kb_1254_870
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 890 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 877 13 h86 kb_1254_877
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 890 30 h87 kb_1254_890
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 928 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 920 8 h88 kb_1254_920
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 928 8 h89 kb_1254_928
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 946 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 936 10 h90 kb_1254_936
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 946 3 h91 kb_1254_946
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 968 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 949 19 h92 kb_1254_949
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 970 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 968 2 h93 kb_1254_968
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 983 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 970 13 h94 kb_1254_970
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 985 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 983 2 h95 kb_1254_983
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1001 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 985 16 h96 kb_1254_985
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1030 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1001 29 h97 kb_1254_1001
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1056 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1030 26 h98 kb_1254_1030
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1056 12 h99 kb_1254_1056
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1068 1 h100 kb_1254_1068
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1070 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1069 1 h101 kb_1254_1069
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1070 2 h102 kb_1254_1070
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1072 29 h103 kb_1254_1072
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1101 2 h104 kb_1254_1101
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1103 6 h105 kb_1254_1103
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1109 6 h106 kb_1254_1109
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1115 85 h107 kb_1254_1115
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1200 33 h108 kb_1254_1200
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1233 12 h109 kb_1254_1233
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1245 2 h110 kb_1254_1245
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1247 1 h111 kb_1254_1247
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1248 1 h112 kb_1254_1248
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1249 3 h113 kb_1254_1249
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1252 16 h114 kb_1254_1252
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1268 4 h115 kb_1254_1268
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1272 1 h116 kb_1254_1272
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1273 17 h117 kb_1254_1273
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1290 12 h118 kb_1254_1290
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1302 3 h119 kb_1254_1302
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1305 7 h120 kb_1254_1305
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1312 5 h121 kb_1254_1312
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1317 10 h122 kb_1254_1317
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1327 3 h123 kb_1254_1327
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1330 7 h124 kb_1254_1330
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1337 8 h125 kb_1254_1337
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1345 8 h126 kb_1254_1345
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1353 7 h127 kb_1254_1353
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1360 33 h128 kb_1254_1360
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1393 26 h129 kb_1254_1393
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1419 18 h130 kb_1254_1419
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1254.lits.getD i 0)) 0 1437 18 h131 kb_1254_1437
    exact h132
  have hg : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1455 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 5 = true := kg_1254_0
    have h1 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 13 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 5 8 h0 kg_1254_5
    have h2 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 21 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 13 8 h1 kg_1254_13
    have h3 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 27 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 21 6 h2 kg_1254_21
    have h4 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 35 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 27 8 h3 kg_1254_27
    have h5 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 49 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 35 14 h4 kg_1254_35
    have h6 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 50 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 49 1 h5 kg_1254_49
    have h7 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 61 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 50 11 h6 kg_1254_50
    have h8 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 82 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 61 21 h7 kg_1254_61
    have h9 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 88 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 82 6 h8 kg_1254_82
    have h10 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 90 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 88 2 h9 kg_1254_88
    have h11 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 111 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 90 21 h10 kg_1254_90
    have h12 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 114 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 111 3 h11 kg_1254_111
    have h13 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 121 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 114 7 h12 kg_1254_114
    have h14 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 128 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 121 7 h13 kg_1254_121
    have h15 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 151 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 128 23 h14 kg_1254_128
    have h16 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 152 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 151 1 h15 kg_1254_151
    have h17 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 157 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 152 5 h16 kg_1254_152
    have h18 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 158 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 157 1 h17 kg_1254_157
    have h19 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 160 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 158 2 h18 kg_1254_158
    have h20 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 162 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 160 2 h19 kg_1254_160
    have h21 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 173 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 162 11 h20 kg_1254_162
    have h22 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 193 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 173 20 h21 kg_1254_173
    have h23 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 201 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 193 8 h22 kg_1254_193
    have h24 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 221 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 201 20 h23 kg_1254_201
    have h25 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 223 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 221 2 h24 kg_1254_221
    have h26 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 235 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 223 12 h25 kg_1254_223
    have h27 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 254 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 235 19 h26 kg_1254_235
    have h28 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 260 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 254 6 h27 kg_1254_254
    have h29 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 262 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 260 2 h28 kg_1254_260
    have h30 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 284 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 262 22 h29 kg_1254_262
    have h31 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 287 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 284 3 h30 kg_1254_284
    have h32 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 288 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 287 1 h31 kg_1254_287
    have h33 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 299 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 288 11 h32 kg_1254_288
    have h34 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 303 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 299 4 h33 kg_1254_299
    have h35 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 315 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 303 12 h34 kg_1254_303
    have h36 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 327 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 315 12 h35 kg_1254_315
    have h37 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 329 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 327 2 h36 kg_1254_327
    have h38 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 341 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 329 12 h37 kg_1254_329
    have h39 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 353 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 341 12 h38 kg_1254_341
    have h40 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 367 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 353 14 h39 kg_1254_353
    have h41 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 373 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 367 6 h40 kg_1254_367
    have h42 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 375 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 373 2 h41 kg_1254_373
    have h43 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 397 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 375 22 h42 kg_1254_375
    have h44 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 399 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 397 2 h43 kg_1254_397
    have h45 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 407 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 399 8 h44 kg_1254_399
    have h46 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 409 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 407 2 h45 kg_1254_407
    have h47 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 430 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 409 21 h46 kg_1254_409
    have h48 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 434 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 430 4 h47 kg_1254_430
    have h49 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 456 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 434 22 h48 kg_1254_434
    have h50 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 457 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 456 1 h49 kg_1254_456
    have h51 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 479 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 457 22 h50 kg_1254_457
    have h52 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 480 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 479 1 h51 kg_1254_479
    have h53 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 482 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 480 2 h52 kg_1254_480
    have h54 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 485 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 482 3 h53 kg_1254_482
    have h55 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 495 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 485 10 h54 kg_1254_485
    have h56 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 504 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 495 9 h55 kg_1254_495
    have h57 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 512 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 504 8 h56 kg_1254_504
    have h58 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 514 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 512 2 h57 kg_1254_512
    have h59 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 515 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 514 1 h58 kg_1254_514
    have h60 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 530 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 515 15 h59 kg_1254_515
    have h61 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 550 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 530 20 h60 kg_1254_530
    have h62 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 553 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 550 3 h61 kg_1254_550
    have h63 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 571 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 553 18 h62 kg_1254_553
    have h64 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 580 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 571 9 h63 kg_1254_571
    have h65 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 584 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 580 4 h64 kg_1254_580
    have h66 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 595 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 584 11 h65 kg_1254_584
    have h67 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 607 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 595 12 h66 kg_1254_595
    have h68 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 618 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 607 11 h67 kg_1254_607
    have h69 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 622 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 618 4 h68 kg_1254_618
    have h70 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 634 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 622 12 h69 kg_1254_622
    have h71 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 645 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 634 11 h70 kg_1254_634
    have h72 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 647 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 645 2 h71 kg_1254_645
    have h73 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 658 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 647 11 h72 kg_1254_647
    have h74 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 664 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 658 6 h73 kg_1254_658
    have h75 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 666 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 664 2 h74 kg_1254_664
    have h76 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 687 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 666 21 h75 kg_1254_666
    have h77 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 695 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 687 8 h76 kg_1254_687
    have h78 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 697 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 695 2 h77 kg_1254_695
    have h79 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 716 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 697 19 h78 kg_1254_697
    have h80 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 748 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 716 32 h79 kg_1254_716
    have h81 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 781 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 748 33 h80 kg_1254_748
    have h82 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 783 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 781 2 h81 kg_1254_781
    have h83 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 789 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 783 6 h82 kg_1254_783
    have h84 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 801 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 789 12 h83 kg_1254_789
    have h85 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 870 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 801 69 h84 kg_1254_801
    have h86 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 877 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 870 7 h85 kg_1254_870
    have h87 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 890 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 877 13 h86 kg_1254_877
    have h88 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 920 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 890 30 h87 kg_1254_890
    have h89 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 928 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 920 8 h88 kg_1254_920
    have h90 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 936 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 928 8 h89 kg_1254_928
    have h91 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 946 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 936 10 h90 kg_1254_936
    have h92 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 949 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 946 3 h91 kg_1254_946
    have h93 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 968 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 949 19 h92 kg_1254_949
    have h94 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 970 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 968 2 h93 kg_1254_968
    have h95 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 983 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 970 13 h94 kg_1254_970
    have h96 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 985 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 983 2 h95 kg_1254_983
    have h97 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1001 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 985 16 h96 kg_1254_985
    have h98 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1030 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1001 29 h97 kg_1254_1001
    have h99 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1056 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1030 26 h98 kg_1254_1030
    have h100 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1068 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1056 12 h99 kg_1254_1056
    have h101 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1069 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1068 1 h100 kg_1254_1068
    have h102 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1070 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1069 1 h101 kg_1254_1069
    have h103 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1072 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1070 2 h102 kg_1254_1070
    have h104 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1101 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1072 29 h103 kg_1254_1072
    have h105 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1103 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1101 2 h104 kg_1254_1101
    have h106 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1109 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1103 6 h105 kg_1254_1103
    have h107 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1115 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1109 6 h106 kg_1254_1109
    have h108 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1200 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1115 85 h107 kg_1254_1115
    have h109 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1233 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1200 33 h108 kg_1254_1200
    have h110 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1245 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1233 12 h109 kg_1254_1233
    have h111 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1247 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1245 2 h110 kg_1254_1245
    have h112 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1248 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1247 1 h111 kg_1254_1247
    have h113 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1249 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1248 1 h112 kg_1254_1248
    have h114 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1252 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1249 3 h113 kg_1254_1249
    have h115 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1268 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1252 16 h114 kg_1254_1252
    have h116 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1272 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1268 4 h115 kg_1254_1268
    have h117 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1273 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1272 1 h116 kg_1254_1272
    have h118 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1290 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1273 17 h117 kg_1254_1273
    have h119 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1302 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1290 12 h118 kg_1254_1290
    have h120 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1305 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1302 3 h119 kg_1254_1302
    have h121 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1312 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1305 7 h120 kg_1254_1305
    have h122 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1317 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1312 5 h121 kg_1254_1312
    have h123 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1327 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1317 10 h122 kg_1254_1317
    have h124 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1330 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1327 3 h123 kg_1254_1327
    have h125 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1337 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1330 7 h124 kg_1254_1330
    have h126 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1345 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1337 8 h125 kg_1254_1337
    have h127 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1353 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1345 8 h126 kg_1254_1345
    have h128 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1360 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1353 7 h127 kg_1254_1353
    have h129 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1393 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1360 33 h128 kg_1254_1360
    have h130 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1419 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1393 26 h129 kg_1254_1393
    have h131 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1437 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1419 18 h130 kg_1254_1419
    have h132 : IPChk.allR (Pts.glueIB K1254.lits KW_1254) 0 1455 = true := IPChk.allR_join (Pts.glueIB K1254.lits KW_1254) 0 1437 18 h131 kg_1254_1437
    exact h132
  have hlen : K1254.lits.length = 1455 := by decide
  intro k h1 h2
  obtain rfl : k = 1254 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1254) K1254.lits KW_1254
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_262 : ∀ k, 1255 ≤ k → k < 1257 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1255 JW_1255 1255 2 jr_1255
theorem jr6_263 : ∀ k, 1257 ≤ k → k < 1258 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 670 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 2 = true := kb_1257_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 2 2 h0 kb_1257_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 4 7 h1 kb_1257_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 11 5 h2 kb_1257_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 16 5 h3 kb_1257_16
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 21 1 h4 kb_1257_21
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 22 1 h5 kb_1257_22
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 23 7 h6 kb_1257_23
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 30 19 h7 kb_1257_30
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 49 5 h8 kb_1257_49
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 54 7 h9 kb_1257_54
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 61 12 h10 kb_1257_61
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 73 13 h11 kb_1257_73
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 86 6 h12 kb_1257_86
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 92 1 h13 kb_1257_92
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 93 37 h14 kb_1257_93
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 130 19 h15 kb_1257_130
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 149 2 h16 kb_1257_149
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 151 13 h17 kb_1257_151
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 164 4 h18 kb_1257_164
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 168 7 h19 kb_1257_168
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 175 16 h20 kb_1257_175
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 191 1 h21 kb_1257_191
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 192 1 h22 kb_1257_192
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 193 1 h23 kb_1257_193
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 194 14 h24 kb_1257_194
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 208 4 h25 kb_1257_208
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 212 12 h26 kb_1257_212
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 224 12 h27 kb_1257_224
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 236 2 h28 kb_1257_236
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 238 12 h29 kb_1257_238
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 250 12 h30 kb_1257_250
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 262 2 h31 kb_1257_262
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 264 12 h32 kb_1257_264
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 276 1 h33 kb_1257_276
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 277 1 h34 kb_1257_277
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 278 1 h35 kb_1257_278
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 279 2 h36 kb_1257_279
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 281 2 h37 kb_1257_281
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 283 1 h38 kb_1257_283
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 284 1 h39 kb_1257_284
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 285 1 h40 kb_1257_285
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 287 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 286 1 h41 kb_1257_286
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 287 1 h42 kb_1257_287
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 288 1 h43 kb_1257_288
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 289 1 h44 kb_1257_289
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 290 1 h45 kb_1257_290
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 291 1 h46 kb_1257_291
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 292 2 h47 kb_1257_292
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 294 2 h48 kb_1257_294
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 296 2 h49 kb_1257_296
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 298 2 h50 kb_1257_298
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 300 1 h51 kb_1257_300
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 301 1 h52 kb_1257_301
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 302 1 h53 kb_1257_302
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 303 2 h54 kb_1257_303
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 305 6 h55 kb_1257_305
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 311 4 h56 kb_1257_311
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 315 11 h57 kb_1257_315
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 326 1 h58 kb_1257_326
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 327 5 h59 kb_1257_327
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 332 2 h60 kb_1257_332
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 334 1 h61 kb_1257_334
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 335 6 h62 kb_1257_335
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 341 24 h63 kb_1257_341
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 365 2 h64 kb_1257_365
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 367 6 h65 kb_1257_367
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 373 3 h66 kb_1257_373
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 376 25 h67 kb_1257_376
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 401 56 h68 kb_1257_401
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 457 16 h69 kb_1257_457
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 473 1 h70 kb_1257_473
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 474 22 h71 kb_1257_474
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 496 3 h72 kb_1257_496
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 499 20 h73 kb_1257_499
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 521 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 519 2 h74 kb_1257_519
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 521 3 h75 kb_1257_521
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 531 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 524 7 h76 kb_1257_524
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 531 7 h77 kb_1257_531
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 538 9 h78 kb_1257_538
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 547 2 h79 kb_1257_547
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 549 8 h80 kb_1257_549
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 557 7 h81 kb_1257_557
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 564 1 h82 kb_1257_564
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 570 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 565 5 h83 kb_1257_565
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 571 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 570 1 h84 kb_1257_570
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 571 2 h85 kb_1257_571
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 573 2 h86 kb_1257_573
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 577 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 575 2 h87 kb_1257_575
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 577 2 h88 kb_1257_577
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 579 1 h89 kb_1257_579
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 581 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 580 1 h90 kb_1257_580
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 581 1 h91 kb_1257_581
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 582 2 h92 kb_1257_582
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 584 1 h93 kb_1257_584
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 585 1 h94 kb_1257_585
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 586 2 h95 kb_1257_586
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 588 1 h96 kb_1257_588
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 590 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 589 1 h97 kb_1257_589
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 590 1 h98 kb_1257_590
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 592 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 591 1 h99 kb_1257_591
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 594 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 592 2 h100 kb_1257_592
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 594 2 h101 kb_1257_594
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 596 5 h102 kb_1257_596
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 601 1 h103 kb_1257_601
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 602 1 h104 kb_1257_602
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 603 4 h105 kb_1257_603
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 607 17 h106 kb_1257_607
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 630 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 624 6 h107 kb_1257_624
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 630 3 h108 kb_1257_630
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 637 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 633 4 h109 kb_1257_633
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 637 3 h110 kb_1257_637
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 640 12 h111 kb_1257_640
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 652 2 h112 kb_1257_652
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 654 1 h113 kb_1257_654
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 655 2 h114 kb_1257_655
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 657 3 h115 kb_1257_657
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 660 1 h116 kb_1257_660
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 661 2 h117 kb_1257_661
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 663 2 h118 kb_1257_663
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 667 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 665 2 h119 kb_1257_665
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1257.lits.getD i 0)) 0 667 3 h120 kb_1257_667
    exact h121
  have hg : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 670 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 2 = true := kg_1257_0
    have h1 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 4 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 2 2 h0 kg_1257_2
    have h2 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 11 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 4 7 h1 kg_1257_4
    have h3 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 16 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 11 5 h2 kg_1257_11
    have h4 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 21 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 16 5 h3 kg_1257_16
    have h5 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 22 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 21 1 h4 kg_1257_21
    have h6 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 23 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 22 1 h5 kg_1257_22
    have h7 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 30 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 23 7 h6 kg_1257_23
    have h8 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 49 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 30 19 h7 kg_1257_30
    have h9 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 54 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 49 5 h8 kg_1257_49
    have h10 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 61 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 54 7 h9 kg_1257_54
    have h11 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 73 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 61 12 h10 kg_1257_61
    have h12 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 86 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 73 13 h11 kg_1257_73
    have h13 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 92 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 86 6 h12 kg_1257_86
    have h14 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 93 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 92 1 h13 kg_1257_92
    have h15 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 130 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 93 37 h14 kg_1257_93
    have h16 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 149 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 130 19 h15 kg_1257_130
    have h17 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 151 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 149 2 h16 kg_1257_149
    have h18 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 164 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 151 13 h17 kg_1257_151
    have h19 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 168 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 164 4 h18 kg_1257_164
    have h20 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 175 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 168 7 h19 kg_1257_168
    have h21 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 191 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 175 16 h20 kg_1257_175
    have h22 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 192 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 191 1 h21 kg_1257_191
    have h23 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 193 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 192 1 h22 kg_1257_192
    have h24 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 194 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 193 1 h23 kg_1257_193
    have h25 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 208 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 194 14 h24 kg_1257_194
    have h26 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 212 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 208 4 h25 kg_1257_208
    have h27 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 224 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 212 12 h26 kg_1257_212
    have h28 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 236 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 224 12 h27 kg_1257_224
    have h29 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 238 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 236 2 h28 kg_1257_236
    have h30 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 250 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 238 12 h29 kg_1257_238
    have h31 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 262 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 250 12 h30 kg_1257_250
    have h32 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 264 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 262 2 h31 kg_1257_262
    have h33 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 276 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 264 12 h32 kg_1257_264
    have h34 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 277 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 276 1 h33 kg_1257_276
    have h35 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 278 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 277 1 h34 kg_1257_277
    have h36 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 279 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 278 1 h35 kg_1257_278
    have h37 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 281 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 279 2 h36 kg_1257_279
    have h38 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 283 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 281 2 h37 kg_1257_281
    have h39 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 284 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 283 1 h38 kg_1257_283
    have h40 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 285 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 284 1 h39 kg_1257_284
    have h41 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 286 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 285 1 h40 kg_1257_285
    have h42 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 287 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 286 1 h41 kg_1257_286
    have h43 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 288 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 287 1 h42 kg_1257_287
    have h44 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 289 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 288 1 h43 kg_1257_288
    have h45 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 290 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 289 1 h44 kg_1257_289
    have h46 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 291 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 290 1 h45 kg_1257_290
    have h47 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 292 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 291 1 h46 kg_1257_291
    have h48 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 294 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 292 2 h47 kg_1257_292
    have h49 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 296 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 294 2 h48 kg_1257_294
    have h50 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 298 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 296 2 h49 kg_1257_296
    have h51 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 300 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 298 2 h50 kg_1257_298
    have h52 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 301 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 300 1 h51 kg_1257_300
    have h53 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 302 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 301 1 h52 kg_1257_301
    have h54 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 303 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 302 1 h53 kg_1257_302
    have h55 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 305 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 303 2 h54 kg_1257_303
    have h56 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 311 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 305 6 h55 kg_1257_305
    have h57 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 315 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 311 4 h56 kg_1257_311
    have h58 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 326 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 315 11 h57 kg_1257_315
    have h59 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 327 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 326 1 h58 kg_1257_326
    have h60 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 332 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 327 5 h59 kg_1257_327
    have h61 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 334 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 332 2 h60 kg_1257_332
    have h62 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 335 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 334 1 h61 kg_1257_334
    have h63 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 341 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 335 6 h62 kg_1257_335
    have h64 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 365 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 341 24 h63 kg_1257_341
    have h65 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 367 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 365 2 h64 kg_1257_365
    have h66 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 373 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 367 6 h65 kg_1257_367
    have h67 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 376 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 373 3 h66 kg_1257_373
    have h68 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 401 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 376 25 h67 kg_1257_376
    have h69 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 457 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 401 56 h68 kg_1257_401
    have h70 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 473 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 457 16 h69 kg_1257_457
    have h71 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 474 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 473 1 h70 kg_1257_473
    have h72 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 496 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 474 22 h71 kg_1257_474
    have h73 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 499 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 496 3 h72 kg_1257_496
    have h74 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 519 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 499 20 h73 kg_1257_499
    have h75 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 521 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 519 2 h74 kg_1257_519
    have h76 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 524 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 521 3 h75 kg_1257_521
    have h77 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 531 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 524 7 h76 kg_1257_524
    have h78 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 538 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 531 7 h77 kg_1257_531
    have h79 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 547 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 538 9 h78 kg_1257_538
    have h80 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 549 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 547 2 h79 kg_1257_547
    have h81 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 557 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 549 8 h80 kg_1257_549
    have h82 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 564 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 557 7 h81 kg_1257_557
    have h83 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 565 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 564 1 h82 kg_1257_564
    have h84 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 570 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 565 5 h83 kg_1257_565
    have h85 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 571 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 570 1 h84 kg_1257_570
    have h86 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 573 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 571 2 h85 kg_1257_571
    have h87 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 575 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 573 2 h86 kg_1257_573
    have h88 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 577 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 575 2 h87 kg_1257_575
    have h89 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 579 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 577 2 h88 kg_1257_577
    have h90 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 580 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 579 1 h89 kg_1257_579
    have h91 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 581 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 580 1 h90 kg_1257_580
    have h92 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 582 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 581 1 h91 kg_1257_581
    have h93 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 584 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 582 2 h92 kg_1257_582
    have h94 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 585 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 584 1 h93 kg_1257_584
    have h95 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 586 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 585 1 h94 kg_1257_585
    have h96 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 588 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 586 2 h95 kg_1257_586
    have h97 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 589 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 588 1 h96 kg_1257_588
    have h98 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 590 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 589 1 h97 kg_1257_589
    have h99 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 591 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 590 1 h98 kg_1257_590
    have h100 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 592 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 591 1 h99 kg_1257_591
    have h101 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 594 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 592 2 h100 kg_1257_592
    have h102 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 596 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 594 2 h101 kg_1257_594
    have h103 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 601 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 596 5 h102 kg_1257_596
    have h104 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 602 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 601 1 h103 kg_1257_601
    have h105 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 603 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 602 1 h104 kg_1257_602
    have h106 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 607 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 603 4 h105 kg_1257_603
    have h107 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 624 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 607 17 h106 kg_1257_607
    have h108 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 630 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 624 6 h107 kg_1257_624
    have h109 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 633 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 630 3 h108 kg_1257_630
    have h110 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 637 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 633 4 h109 kg_1257_633
    have h111 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 640 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 637 3 h110 kg_1257_637
    have h112 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 652 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 640 12 h111 kg_1257_640
    have h113 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 654 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 652 2 h112 kg_1257_652
    have h114 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 655 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 654 1 h113 kg_1257_654
    have h115 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 657 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 655 2 h114 kg_1257_655
    have h116 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 660 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 657 3 h115 kg_1257_657
    have h117 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 661 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 660 1 h116 kg_1257_660
    have h118 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 663 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 661 2 h117 kg_1257_661
    have h119 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 665 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 663 2 h118 kg_1257_663
    have h120 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 667 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 665 2 h119 kg_1257_665
    have h121 : IPChk.allR (Pts.glueIB K1257.lits KW_1257) 0 670 = true := IPChk.allR_join (Pts.glueIB K1257.lits KW_1257) 0 667 3 h120 kg_1257_667
    exact h121
  have hlen : K1257.lits.length = 670 := by decide
  intro k h1 h2
  obtain rfl : k = 1257 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1257) K1257.lits KW_1257
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_264 : ∀ k, 1258 ≤ k → k < 1259 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1258 JW_1258 1258 1 jr_1258
theorem jr6_265 : ∀ k, 1259 ≤ k → k < 1260 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 542 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 2 = true := kb_1259_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 2 7 h0 kb_1259_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 9 11 h1 kb_1259_9
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 20 2 h2 kb_1259_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 22 6 h3 kb_1259_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 28 2 h4 kb_1259_28
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 30 31 h5 kb_1259_30
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 61 9 h6 kb_1259_61
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 70 6 h7 kb_1259_70
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 76 18 h8 kb_1259_76
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 94 9 h9 kb_1259_94
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 103 16 h10 kb_1259_103
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 119 6 h11 kb_1259_119
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 125 2 h12 kb_1259_125
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 127 22 h13 kb_1259_127
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 149 1 h14 kb_1259_149
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 150 1 h15 kb_1259_150
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 151 1 h16 kb_1259_151
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 152 13 h17 kb_1259_152
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 165 2 h18 kb_1259_165
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 167 22 h19 kb_1259_167
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 189 7 h20 kb_1259_189
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 196 15 h21 kb_1259_196
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 211 31 h22 kb_1259_211
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 242 17 h23 kb_1259_242
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 259 2 h24 kb_1259_259
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 261 1 h25 kb_1259_261
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 262 13 h26 kb_1259_262
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 275 4 h27 kb_1259_275
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 279 6 h28 kb_1259_279
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 285 45 h29 kb_1259_285
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 330 9 h30 kb_1259_330
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 339 14 h31 kb_1259_339
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 353 9 h32 kb_1259_353
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 362 6 h33 kb_1259_362
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 368 16 h34 kb_1259_368
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 386 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 384 2 h35 kb_1259_384
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 394 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 386 8 h36 kb_1259_386
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 394 14 h37 kb_1259_394
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 408 1 h38 kb_1259_408
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 409 15 h39 kb_1259_409
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 424 5 h40 kb_1259_424
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 429 2 h41 kb_1259_429
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 431 1 h42 kb_1259_431
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 432 21 h43 kb_1259_432
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 453 13 h44 kb_1259_453
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 466 17 h45 kb_1259_466
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 483 11 h46 kb_1259_483
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 513 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 494 19 h47 kb_1259_494
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 513 9 h48 kb_1259_513
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 522 17 h49 kb_1259_522
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 541 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 539 2 h50 kb_1259_539
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 542 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1259.lits.getD i 0)) 0 541 1 h51 kb_1259_541
    exact h52
  have hg : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 542 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 2 = true := kg_1259_0
    have h1 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 9 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 2 7 h0 kg_1259_2
    have h2 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 20 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 9 11 h1 kg_1259_9
    have h3 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 22 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 20 2 h2 kg_1259_20
    have h4 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 28 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 22 6 h3 kg_1259_22
    have h5 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 30 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 28 2 h4 kg_1259_28
    have h6 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 61 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 30 31 h5 kg_1259_30
    have h7 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 70 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 61 9 h6 kg_1259_61
    have h8 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 76 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 70 6 h7 kg_1259_70
    have h9 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 94 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 76 18 h8 kg_1259_76
    have h10 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 103 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 94 9 h9 kg_1259_94
    have h11 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 119 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 103 16 h10 kg_1259_103
    have h12 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 125 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 119 6 h11 kg_1259_119
    have h13 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 127 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 125 2 h12 kg_1259_125
    have h14 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 149 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 127 22 h13 kg_1259_127
    have h15 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 150 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 149 1 h14 kg_1259_149
    have h16 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 151 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 150 1 h15 kg_1259_150
    have h17 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 152 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 151 1 h16 kg_1259_151
    have h18 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 165 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 152 13 h17 kg_1259_152
    have h19 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 167 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 165 2 h18 kg_1259_165
    have h20 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 189 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 167 22 h19 kg_1259_167
    have h21 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 196 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 189 7 h20 kg_1259_189
    have h22 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 211 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 196 15 h21 kg_1259_196
    have h23 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 242 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 211 31 h22 kg_1259_211
    have h24 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 259 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 242 17 h23 kg_1259_242
    have h25 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 261 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 259 2 h24 kg_1259_259
    have h26 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 262 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 261 1 h25 kg_1259_261
    have h27 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 275 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 262 13 h26 kg_1259_262
    have h28 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 279 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 275 4 h27 kg_1259_275
    have h29 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 285 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 279 6 h28 kg_1259_279
    have h30 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 330 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 285 45 h29 kg_1259_285
    have h31 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 339 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 330 9 h30 kg_1259_330
    have h32 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 353 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 339 14 h31 kg_1259_339
    have h33 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 362 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 353 9 h32 kg_1259_353
    have h34 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 368 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 362 6 h33 kg_1259_362
    have h35 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 384 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 368 16 h34 kg_1259_368
    have h36 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 386 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 384 2 h35 kg_1259_384
    have h37 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 394 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 386 8 h36 kg_1259_386
    have h38 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 408 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 394 14 h37 kg_1259_394
    have h39 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 409 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 408 1 h38 kg_1259_408
    have h40 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 424 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 409 15 h39 kg_1259_409
    have h41 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 429 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 424 5 h40 kg_1259_424
    have h42 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 431 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 429 2 h41 kg_1259_429
    have h43 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 432 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 431 1 h42 kg_1259_431
    have h44 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 453 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 432 21 h43 kg_1259_432
    have h45 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 466 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 453 13 h44 kg_1259_453
    have h46 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 483 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 466 17 h45 kg_1259_466
    have h47 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 494 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 483 11 h46 kg_1259_483
    have h48 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 513 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 494 19 h47 kg_1259_494
    have h49 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 522 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 513 9 h48 kg_1259_513
    have h50 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 539 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 522 17 h49 kg_1259_522
    have h51 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 541 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 539 2 h50 kg_1259_539
    have h52 : IPChk.allR (Pts.glueIB K1259.lits KW_1259) 0 542 = true := IPChk.allR_join (Pts.glueIB K1259.lits KW_1259) 0 541 1 h51 kg_1259_541
    exact h52
  have hlen : K1259.lits.length = 542 := by decide
  intro k h1 h2
  obtain rfl : k = 1259 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1259) K1259.lits KW_1259
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_266 : ∀ k, 1260 ≤ k → k < 1265 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1260 JW_1260 1260 5 jr_1260
theorem jr6_267 : ∀ k, 1265 ≤ k → k < 1266 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 122 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 1 = true := kb_1265_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 1 9 h0 kb_1265_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 10 18 h1 kb_1265_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 28 22 h2 kb_1265_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 50 10 h3 kb_1265_50
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 60 9 h4 kb_1265_60
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 69 1 h5 kb_1265_69
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 70 15 h6 kb_1265_70
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 85 13 h7 kb_1265_85
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 98 1 h8 kb_1265_98
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 99 1 h9 kb_1265_99
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 100 1 h10 kb_1265_100
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 101 2 h11 kb_1265_101
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 103 1 h12 kb_1265_103
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 104 1 h13 kb_1265_104
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 105 1 h14 kb_1265_105
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 106 1 h15 kb_1265_106
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 107 2 h16 kb_1265_107
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 109 2 h17 kb_1265_109
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 111 2 h18 kb_1265_111
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 113 3 h19 kb_1265_113
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 116 2 h20 kb_1265_116
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 118 3 h21 kb_1265_118
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1265.lits.getD i 0)) 0 121 1 h22 kb_1265_121
    exact h23
  have hg : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 122 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 1 = true := kg_1265_0
    have h1 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 10 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 1 9 h0 kg_1265_1
    have h2 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 28 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 10 18 h1 kg_1265_10
    have h3 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 50 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 28 22 h2 kg_1265_28
    have h4 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 60 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 50 10 h3 kg_1265_50
    have h5 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 69 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 60 9 h4 kg_1265_60
    have h6 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 70 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 69 1 h5 kg_1265_69
    have h7 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 85 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 70 15 h6 kg_1265_70
    have h8 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 98 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 85 13 h7 kg_1265_85
    have h9 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 99 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 98 1 h8 kg_1265_98
    have h10 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 100 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 99 1 h9 kg_1265_99
    have h11 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 101 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 100 1 h10 kg_1265_100
    have h12 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 103 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 101 2 h11 kg_1265_101
    have h13 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 104 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 103 1 h12 kg_1265_103
    have h14 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 105 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 104 1 h13 kg_1265_104
    have h15 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 106 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 105 1 h14 kg_1265_105
    have h16 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 107 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 106 1 h15 kg_1265_106
    have h17 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 109 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 107 2 h16 kg_1265_107
    have h18 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 111 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 109 2 h17 kg_1265_109
    have h19 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 113 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 111 2 h18 kg_1265_111
    have h20 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 116 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 113 3 h19 kg_1265_113
    have h21 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 118 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 116 2 h20 kg_1265_116
    have h22 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 121 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 118 3 h21 kg_1265_118
    have h23 : IPChk.allR (Pts.glueIB K1265.lits KW_1265) 0 122 = true := IPChk.allR_join (Pts.glueIB K1265.lits KW_1265) 0 121 1 h22 kg_1265_121
    exact h23
  have hlen : K1265.lits.length = 122 := by decide
  intro k h1 h2
  obtain rfl : k = 1265 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1265) K1265.lits KW_1265
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_268 : ∀ k, 1266 ≤ k → k < 1282 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1266 JW_1266 1266 16 jr_1266
theorem jr6_269 : ∀ k, 1282 ≤ k → k < 1283 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 7 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 1 = true := kb_1282_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 1 1 h0 kb_1282_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 2 1 h1 kb_1282_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 3 2 h2 kb_1282_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1282.lits.getD i 0)) 0 5 2 h3 kb_1282_5
    exact h4
  have hg : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 7 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 1 = true := kg_1282_0
    have h1 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 2 = true := IPChk.allR_join (Pts.glueIB K1282.lits KW_1282) 0 1 1 h0 kg_1282_1
    have h2 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 3 = true := IPChk.allR_join (Pts.glueIB K1282.lits KW_1282) 0 2 1 h1 kg_1282_2
    have h3 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 5 = true := IPChk.allR_join (Pts.glueIB K1282.lits KW_1282) 0 3 2 h2 kg_1282_3
    have h4 : IPChk.allR (Pts.glueIB K1282.lits KW_1282) 0 7 = true := IPChk.allR_join (Pts.glueIB K1282.lits KW_1282) 0 5 2 h3 kg_1282_5
    exact h4
  have hlen : K1282.lits.length = 7 := by decide
  intro k h1 h2
  obtain rfl : k = 1282 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1282) K1282.lits KW_1282
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_270 : ∀ k, 1283 ≤ k → k < 1286 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1283 3 jr_1283
theorem jr6_271 : ∀ k, 1286 ≤ k → k < 1301 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1286 15 jr_1286
theorem jr6_272 : ∀ k, 1301 ≤ k → k < 1318 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1301 17 jr_1301
theorem jr6_273 : ∀ k, 1318 ≤ k → k < 1330 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1318 12 jr_1318
theorem jr6_274 : ∀ k, 1330 ≤ k → k < 1342 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1330 12 jr_1330
theorem jr6_275 : ∀ k, 1342 ≤ k → k < 1344 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1283 JW_1283 1342 2 jr_1342
theorem jr6_276 : ∀ k, 1344 ≤ k → k < 1345 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 787 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 5 = true := kb_1344_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 5 6 h0 kb_1344_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 11 10 h1 kb_1344_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 21 1 h2 kb_1344_21
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 22 1 h3 kb_1344_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 23 1 h4 kb_1344_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 24 12 h5 kb_1344_24
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 36 4 h6 kb_1344_36
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 40 12 h7 kb_1344_40
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 52 9 h8 kb_1344_52
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 61 2 h9 kb_1344_61
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 63 6 h10 kb_1344_63
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 69 2 h11 kb_1344_69
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 71 21 h12 kb_1344_71
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 92 8 h13 kb_1344_92
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 100 18 h14 kb_1344_100
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 118 1 h15 kb_1344_118
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 119 7 h16 kb_1344_119
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 126 1 h17 kb_1344_126
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 127 56 h18 kb_1344_127
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 183 60 h19 kb_1344_183
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 243 1 h20 kb_1344_243
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 244 29 h21 kb_1344_244
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 273 2 h22 kb_1344_273
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 275 6 h23 kb_1344_275
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 281 2 h24 kb_1344_281
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 283 20 h25 kb_1344_283
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 303 5 h26 kb_1344_303
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 308 27 h27 kb_1344_308
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 335 40 h28 kb_1344_335
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 375 2 h29 kb_1344_375
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 377 15 h30 kb_1344_377
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 392 7 h31 kb_1344_392
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 399 19 h32 kb_1344_399
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 418 5 h33 kb_1344_418
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 423 40 h34 kb_1344_423
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 463 4 h35 kb_1344_463
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 467 1 h36 kb_1344_467
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 468 52 h37 kb_1344_468
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 590 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 520 70 h38 kb_1344_520
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 594 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 590 4 h39 kb_1344_590
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 594 2 h40 kb_1344_594
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 596 12 h41 kb_1344_596
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 608 1 h42 kb_1344_608
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 609 2 h43 kb_1344_609
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 623 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 611 12 h44 kb_1344_611
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 628 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 623 5 h45 kb_1344_623
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 632 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 628 4 h46 kb_1344_628
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 632 11 h47 kb_1344_632
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 643 7 h48 kb_1344_643
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 650 8 h49 kb_1344_650
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 658 7 h50 kb_1344_658
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 665 19 h51 kb_1344_665
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 684 7 h52 kb_1344_684
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 691 31 h53 kb_1344_691
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 728 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 722 6 h54 kb_1344_722
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 728 12 h55 kb_1344_728
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 755 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 740 15 h56 kb_1344_740
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 760 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 755 5 h57 kb_1344_755
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 760 18 h58 kb_1344_760
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 778 3 h59 kb_1344_778
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 781 3 h60 kb_1344_781
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1344.lits.getD i 0)) 0 784 3 h61 kb_1344_784
    exact h62
  have hg : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 787 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 5 = true := kg_1344_0
    have h1 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 11 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 5 6 h0 kg_1344_5
    have h2 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 21 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 11 10 h1 kg_1344_11
    have h3 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 22 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 21 1 h2 kg_1344_21
    have h4 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 23 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 22 1 h3 kg_1344_22
    have h5 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 24 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 23 1 h4 kg_1344_23
    have h6 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 36 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 24 12 h5 kg_1344_24
    have h7 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 40 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 36 4 h6 kg_1344_36
    have h8 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 52 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 40 12 h7 kg_1344_40
    have h9 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 61 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 52 9 h8 kg_1344_52
    have h10 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 63 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 61 2 h9 kg_1344_61
    have h11 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 69 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 63 6 h10 kg_1344_63
    have h12 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 71 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 69 2 h11 kg_1344_69
    have h13 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 92 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 71 21 h12 kg_1344_71
    have h14 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 100 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 92 8 h13 kg_1344_92
    have h15 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 118 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 100 18 h14 kg_1344_100
    have h16 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 119 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 118 1 h15 kg_1344_118
    have h17 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 126 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 119 7 h16 kg_1344_119
    have h18 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 127 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 126 1 h17 kg_1344_126
    have h19 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 183 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 127 56 h18 kg_1344_127
    have h20 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 243 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 183 60 h19 kg_1344_183
    have h21 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 244 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 243 1 h20 kg_1344_243
    have h22 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 273 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 244 29 h21 kg_1344_244
    have h23 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 275 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 273 2 h22 kg_1344_273
    have h24 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 281 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 275 6 h23 kg_1344_275
    have h25 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 283 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 281 2 h24 kg_1344_281
    have h26 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 303 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 283 20 h25 kg_1344_283
    have h27 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 308 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 303 5 h26 kg_1344_303
    have h28 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 335 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 308 27 h27 kg_1344_308
    have h29 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 375 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 335 40 h28 kg_1344_335
    have h30 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 377 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 375 2 h29 kg_1344_375
    have h31 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 392 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 377 15 h30 kg_1344_377
    have h32 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 399 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 392 7 h31 kg_1344_392
    have h33 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 418 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 399 19 h32 kg_1344_399
    have h34 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 423 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 418 5 h33 kg_1344_418
    have h35 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 463 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 423 40 h34 kg_1344_423
    have h36 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 467 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 463 4 h35 kg_1344_463
    have h37 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 468 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 467 1 h36 kg_1344_467
    have h38 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 520 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 468 52 h37 kg_1344_468
    have h39 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 590 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 520 70 h38 kg_1344_520
    have h40 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 594 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 590 4 h39 kg_1344_590
    have h41 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 596 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 594 2 h40 kg_1344_594
    have h42 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 608 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 596 12 h41 kg_1344_596
    have h43 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 609 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 608 1 h42 kg_1344_608
    have h44 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 611 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 609 2 h43 kg_1344_609
    have h45 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 623 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 611 12 h44 kg_1344_611
    have h46 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 628 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 623 5 h45 kg_1344_623
    have h47 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 632 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 628 4 h46 kg_1344_628
    have h48 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 643 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 632 11 h47 kg_1344_632
    have h49 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 650 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 643 7 h48 kg_1344_643
    have h50 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 658 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 650 8 h49 kg_1344_650
    have h51 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 665 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 658 7 h50 kg_1344_658
    have h52 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 684 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 665 19 h51 kg_1344_665
    have h53 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 691 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 684 7 h52 kg_1344_684
    have h54 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 722 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 691 31 h53 kg_1344_691
    have h55 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 728 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 722 6 h54 kg_1344_722
    have h56 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 740 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 728 12 h55 kg_1344_728
    have h57 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 755 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 740 15 h56 kg_1344_740
    have h58 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 760 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 755 5 h57 kg_1344_755
    have h59 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 778 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 760 18 h58 kg_1344_760
    have h60 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 781 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 778 3 h59 kg_1344_778
    have h61 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 784 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 781 3 h60 kg_1344_781
    have h62 : IPChk.allR (Pts.glueIB K1344.lits KW_1344) 0 787 = true := IPChk.allR_join (Pts.glueIB K1344.lits KW_1344) 0 784 3 h61 kg_1344_784
    exact h62
  have hlen : K1344.lits.length = 787 := by decide
  intro k h1 h2
  obtain rfl : k = 1344 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1344) K1344.lits KW_1344
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_277 : ∀ k, 1345 ≤ k → k < 1347 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1345 JW_1345 1345 2 jr_1345

theorem grp6_9 : ∀ k, 1252 ≤ k → k < 1347 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_259
  have a1 := Pts.fa_join a0 jr6_260
  have a2 := Pts.fa_join a1 jr6_261
  have a3 := Pts.fa_join a2 jr6_262
  have a4 := Pts.fa_join a3 jr6_263
  have a5 := Pts.fa_join a4 jr6_264
  have a6 := Pts.fa_join a5 jr6_265
  have a7 := Pts.fa_join a6 jr6_266
  have a8 := Pts.fa_join a7 jr6_267
  have a9 := Pts.fa_join a8 jr6_268
  have a10 := Pts.fa_join a9 jr6_269
  have a11 := Pts.fa_join a10 jr6_270
  have a12 := Pts.fa_join a11 jr6_271
  have a13 := Pts.fa_join a12 jr6_272
  have a14 := Pts.fa_join a13 jr6_273
  have a15 := Pts.fa_join a14 jr6_274
  have a16 := Pts.fa_join a15 jr6_275
  have a17 := Pts.fa_join a16 jr6_276
  have a18 := Pts.fa_join a17 jr6_277
  exact a18

end B334.E1x.Pts.S707
