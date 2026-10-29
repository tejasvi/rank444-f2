import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J1408
import B334.E1x.Pts.S707.J1410
import B334.E1x.Pts.S707.J1414
import B334.E1x.Pts.S707.J1416
import B334.E1x.Pts.S707.J1460
import B334.E1x.Pts.S707.K1406L
import B334.E1x.Pts.S707.K1407L
import B334.E1x.Pts.S707.K1409L
import B334.E1x.Pts.S707.K1412L
import B334.E1x.Pts.S707.K1413L
import B334.E1x.Pts.S707.K1415L
import B334.E1x.Pts.S707.K1459L
import B334.E1x.Pts.S707.K1462L
import B334.E1x.Pts.S707.K1406Q0
import B334.E1x.Pts.S707.K1406Q1
import B334.E1x.Pts.S707.K1406Q2
import B334.E1x.Pts.S707.K1406Q3
import B334.E1x.Pts.S707.K1406Q4
import B334.E1x.Pts.S707.K1406Q5
import B334.E1x.Pts.S707.K1406Q6
import B334.E1x.Pts.S707.K1406Q7
import B334.E1x.Pts.S707.K1406Q8
import B334.E1x.Pts.S707.K1406Q9
import B334.E1x.Pts.S707.K1407Q0
import B334.E1x.Pts.S707.K1407Q1
import B334.E1x.Pts.S707.K1407Q2
import B334.E1x.Pts.S707.K1407Q3
import B334.E1x.Pts.S707.K1407Q4
import B334.E1x.Pts.S707.K1407Q5
import B334.E1x.Pts.S707.K1407Q6
import B334.E1x.Pts.S707.K1407Q7
import B334.E1x.Pts.S707.K1407Q8
import B334.E1x.Pts.S707.K1407Q9
import B334.E1x.Pts.S707.K1409Q0
import B334.E1x.Pts.S707.K1409Q1
import B334.E1x.Pts.S707.K1409Q2
import B334.E1x.Pts.S707.K1409Q3
import B334.E1x.Pts.S707.K1409Q4
import B334.E1x.Pts.S707.K1409Q5
import B334.E1x.Pts.S707.K1412Q0
import B334.E1x.Pts.S707.K1412Q1
import B334.E1x.Pts.S707.K1413Q0
import B334.E1x.Pts.S707.K1413Q1
import B334.E1x.Pts.S707.K1413Q2
import B334.E1x.Pts.S707.K1415Q0
import B334.E1x.Pts.S707.K1415Q1
import B334.E1x.Pts.S707.K1415Q2
import B334.E1x.Pts.S707.K1415Q3
import B334.E1x.Pts.S707.K1415Q4
import B334.E1x.Pts.S707.K1415Q5
import B334.E1x.Pts.S707.K1459Q0
import B334.E1x.Pts.S707.K1459Q1
import B334.E1x.Pts.S707.K1459Q2
import B334.E1x.Pts.S707.K1459Q3
import B334.E1x.Pts.S707.K1459Q4
import B334.E1x.Pts.S707.K1459Q5
import B334.E1x.Pts.S707.K1459Q6
import B334.E1x.Pts.S707.K1459Q7
import B334.E1x.Pts.S707.K1459Q8
import B334.E1x.Pts.S707.K1459Q9
import B334.E1x.Pts.S707.K1462Q0
import B334.E1x.Pts.S707.K1462Q1
import B334.E1x.Pts.S707.K1462Q2
import B334.E1x.Pts.S707.K1462Q3
import B334.E1x.Pts.S707.K1462Q4
import B334.E1x.Pts.S707.K1462Q5
import B334.E1x.Pts.S707.K1406Q10
import B334.E1x.Pts.S707.K1406Q11
import B334.E1x.Pts.S707.K1406Q12
import B334.E1x.Pts.S707.K1406Q13
import B334.E1x.Pts.S707.K1406Q14
import B334.E1x.Pts.S707.K1406Q15
import B334.E1x.Pts.S707.K1407Q10
import B334.E1x.Pts.S707.K1407Q11
import B334.E1x.Pts.S707.K1407Q12
import B334.E1x.Pts.S707.K1407Q13
import B334.E1x.Pts.S707.K1407Q14
import B334.E1x.Pts.S707.K1407Q15
import B334.E1x.Pts.S707.K1407Q16
import B334.E1x.Pts.S707.K1407Q17
import B334.E1x.Pts.S707.K1407Q18
import B334.E1x.Pts.S707.K1407Q19
import B334.E1x.Pts.S707.K1407Q20
import B334.E1x.Pts.S707.K1407Q21
import B334.E1x.Pts.S707.K1407Q22

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 1406 … 1462 (stage707_v6): the v5 Fin's job blocks r287 … r299 as
theorems, joined into `grp6_11` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_287 : ∀ k, 1406 ≤ k → k < 1407 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1603 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 5 = true := kb_1406_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 5 6 h0 kb_1406_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 11 12 h1 kb_1406_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 23 4 h2 kb_1406_23
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 27 15 h3 kb_1406_27
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 42 6 h4 kb_1406_42
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 48 13 h5 kb_1406_48
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 61 16 h6 kb_1406_61
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 77 2 h7 kb_1406_77
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 79 6 h8 kb_1406_79
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 85 21 h9 kb_1406_85
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 106 24 h10 kb_1406_106
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 130 6 h11 kb_1406_130
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 136 2 h12 kb_1406_136
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 138 17 h13 kb_1406_138
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 155 7 h14 kb_1406_155
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 162 4 h15 kb_1406_162
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 166 4 h16 kb_1406_166
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 170 6 h17 kb_1406_170
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 176 6 h18 kb_1406_176
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 182 7 h19 kb_1406_182
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 189 1 h20 kb_1406_189
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 190 1 h21 kb_1406_190
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 191 13 h22 kb_1406_191
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 204 12 h23 kb_1406_204
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 216 6 h24 kb_1406_216
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 222 2 h25 kb_1406_222
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 224 20 h26 kb_1406_224
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 244 1 h27 kb_1406_244
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 245 3 h28 kb_1406_245
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 248 1 h29 kb_1406_248
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 249 2 h30 kb_1406_249
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 251 2 h31 kb_1406_251
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 253 21 h32 kb_1406_253
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 274 3 h33 kb_1406_274
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 277 6 h34 kb_1406_277
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 283 2 h35 kb_1406_283
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 285 20 h36 kb_1406_285
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 305 1 h37 kb_1406_305
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 306 2 h38 kb_1406_306
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 308 40 h39 kb_1406_308
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 348 2 h40 kb_1406_348
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 350 14 h41 kb_1406_350
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 364 2 h42 kb_1406_364
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 366 6 h43 kb_1406_366
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 372 2 h44 kb_1406_372
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 374 22 h45 kb_1406_374
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 396 2 h46 kb_1406_396
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 398 8 h47 kb_1406_398
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 406 23 h48 kb_1406_406
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 429 23 h49 kb_1406_429
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 452 24 h50 kb_1406_452
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 478 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 476 2 h51 kb_1406_476
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 478 6 h52 kb_1406_478
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 484 5 h53 kb_1406_484
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 489 3 h54 kb_1406_489
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 492 4 h55 kb_1406_492
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 496 1 h56 kb_1406_496
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 497 7 h57 kb_1406_497
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 504 5 h58 kb_1406_504
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 509 10 h59 kb_1406_509
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 519 3 h60 kb_1406_519
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 522 29 h61 kb_1406_522
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 551 2 h62 kb_1406_551
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 553 6 h63 kb_1406_553
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 559 2 h64 kb_1406_559
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 561 49 h65 kb_1406_561
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 610 25 h66 kb_1406_610
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 635 11 h67 kb_1406_635
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 646 14 h68 kb_1406_646
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 660 2 h69 kb_1406_660
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 662 20 h70 kb_1406_662
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 682 2 h71 kb_1406_682
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 698 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 684 14 h72 kb_1406_684
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 704 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 698 6 h73 kb_1406_698
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 704 2 h74 kb_1406_704
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 706 25 h75 kb_1406_706
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 731 2 h76 kb_1406_731
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 752 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 733 19 h77 kb_1406_733
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 754 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 752 2 h78 kb_1406_752
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 754 32 h79 kb_1406_754
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 792 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 786 6 h80 kb_1406_786
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 806 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 792 14 h81 kb_1406_792
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 806 2 h82 kb_1406_806
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 821 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 808 13 h83 kb_1406_808
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 821 6 h84 kb_1406_821
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 827 2 h85 kb_1406_827
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 829 12 h86 kb_1406_829
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 845 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 841 4 h87 kb_1406_841
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 845 22 h88 kb_1406_845
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 883 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 867 16 h89 kb_1406_867
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 906 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 883 23 h90 kb_1406_883
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 915 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 906 9 h91 kb_1406_906
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 939 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 915 24 h92 kb_1406_915
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 961 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 939 22 h93 kb_1406_939
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 961 2 h94 kb_1406_961
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 963 15 h95 kb_1406_963
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 997 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 978 19 h96 kb_1406_978
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 997 16 h97 kb_1406_997
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1017 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1013 4 h98 kb_1406_1013
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1050 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1017 33 h99 kb_1406_1017
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1050 21 h100 kb_1406_1050
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1073 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1071 2 h101 kb_1406_1071
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1074 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1073 1 h102 kb_1406_1073
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1075 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1074 1 h103 kb_1406_1074
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1076 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1075 1 h104 kb_1406_1075
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1077 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1076 1 h105 kb_1406_1076
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1078 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1077 1 h106 kb_1406_1077
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1080 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1078 2 h107 kb_1406_1078
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1080 2 h108 kb_1406_1080
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1084 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1082 2 h109 kb_1406_1082
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1085 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1084 1 h110 kb_1406_1084
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1087 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1085 2 h111 kb_1406_1085
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1088 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1087 1 h112 kb_1406_1087
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1093 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1088 5 h113 kb_1406_1088
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1096 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1093 3 h114 kb_1406_1093
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1096 1 h115 kb_1406_1096
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1097 6 h116 kb_1406_1097
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1103 1 h117 kb_1406_1103
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1104 11 h118 kb_1406_1104
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1115 3 h119 kb_1406_1115
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1118 1 h120 kb_1406_1118
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1119 3 h121 kb_1406_1119
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1122 12 h122 kb_1406_1122
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1134 2 h123 kb_1406_1134
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1136 13 h124 kb_1406_1136
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1149 6 h125 kb_1406_1149
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1155 1 h126 kb_1406_1155
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1156 15 h127 kb_1406_1156
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1171 1 h128 kb_1406_1171
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1172 33 h129 kb_1406_1172
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1205 21 h130 kb_1406_1205
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1226 32 h131 kb_1406_1226
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1258 5 h132 kb_1406_1258
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1287 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1263 24 h133 kb_1406_1263
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1287 12 h134 kb_1406_1287
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1299 31 h135 kb_1406_1299
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1330 33 h136 kb_1406_1330
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1363 8 h137 kb_1406_1363
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1371 12 h138 kb_1406_1371
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1383 56 h139 kb_1406_1383
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1439 33 h140 kb_1406_1439
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1472 13 h141 kb_1406_1472
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1485 1 h142 kb_1406_1485
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1486 1 h143 kb_1406_1486
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1487 2 h144 kb_1406_1487
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1489 4 h145 kb_1406_1489
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1493 4 h146 kb_1406_1493
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1498 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1497 1 h147 kb_1406_1497
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1498 7 h148 kb_1406_1498
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1505 2 h149 kb_1406_1505
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1507 2 h150 kb_1406_1507
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1510 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1509 1 h151 kb_1406_1509
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1510 8 h152 kb_1406_1510
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1518 17 h153 kb_1406_1518
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1535 5 h154 kb_1406_1535
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1540 20 h155 kb_1406_1540
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1560 23 h156 kb_1406_1560
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 0 1583 20 h157 kb_1406_1583
    exact h158
  have hg : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1603 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 5 = true := kg_1406_0
    have h1 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 11 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 5 6 h0 kg_1406_5
    have h2 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 23 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 11 12 h1 kg_1406_11
    have h3 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 27 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 23 4 h2 kg_1406_23
    have h4 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 42 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 27 15 h3 kg_1406_27
    have h5 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 48 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 42 6 h4 kg_1406_42
    have h6 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 61 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 48 13 h5 kg_1406_48
    have h7 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 77 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 61 16 h6 kg_1406_61
    have h8 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 79 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 77 2 h7 kg_1406_77
    have h9 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 85 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 79 6 h8 kg_1406_79
    have h10 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 106 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 85 21 h9 kg_1406_85
    have h11 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 130 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 106 24 h10 kg_1406_106
    have h12 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 136 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 130 6 h11 kg_1406_130
    have h13 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 138 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 136 2 h12 kg_1406_136
    have h14 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 155 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 138 17 h13 kg_1406_138
    have h15 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 162 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 155 7 h14 kg_1406_155
    have h16 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 166 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 162 4 h15 kg_1406_162
    have h17 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 170 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 166 4 h16 kg_1406_166
    have h18 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 176 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 170 6 h17 kg_1406_170
    have h19 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 182 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 176 6 h18 kg_1406_176
    have h20 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 189 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 182 7 h19 kg_1406_182
    have h21 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 190 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 189 1 h20 kg_1406_189
    have h22 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 191 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 190 1 h21 kg_1406_190
    have h23 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 204 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 191 13 h22 kg_1406_191
    have h24 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 216 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 204 12 h23 kg_1406_204
    have h25 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 222 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 216 6 h24 kg_1406_216
    have h26 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 224 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 222 2 h25 kg_1406_222
    have h27 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 244 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 224 20 h26 kg_1406_224
    have h28 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 245 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 244 1 h27 kg_1406_244
    have h29 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 248 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 245 3 h28 kg_1406_245
    have h30 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 249 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 248 1 h29 kg_1406_248
    have h31 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 251 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 249 2 h30 kg_1406_249
    have h32 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 253 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 251 2 h31 kg_1406_251
    have h33 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 274 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 253 21 h32 kg_1406_253
    have h34 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 277 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 274 3 h33 kg_1406_274
    have h35 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 283 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 277 6 h34 kg_1406_277
    have h36 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 285 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 283 2 h35 kg_1406_283
    have h37 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 305 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 285 20 h36 kg_1406_285
    have h38 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 306 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 305 1 h37 kg_1406_305
    have h39 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 308 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 306 2 h38 kg_1406_306
    have h40 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 348 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 308 40 h39 kg_1406_308
    have h41 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 350 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 348 2 h40 kg_1406_348
    have h42 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 364 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 350 14 h41 kg_1406_350
    have h43 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 366 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 364 2 h42 kg_1406_364
    have h44 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 372 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 366 6 h43 kg_1406_366
    have h45 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 374 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 372 2 h44 kg_1406_372
    have h46 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 396 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 374 22 h45 kg_1406_374
    have h47 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 398 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 396 2 h46 kg_1406_396
    have h48 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 406 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 398 8 h47 kg_1406_398
    have h49 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 429 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 406 23 h48 kg_1406_406
    have h50 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 452 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 429 23 h49 kg_1406_429
    have h51 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 476 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 452 24 h50 kg_1406_452
    have h52 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 478 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 476 2 h51 kg_1406_476
    have h53 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 484 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 478 6 h52 kg_1406_478
    have h54 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 489 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 484 5 h53 kg_1406_484
    have h55 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 492 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 489 3 h54 kg_1406_489
    have h56 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 496 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 492 4 h55 kg_1406_492
    have h57 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 497 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 496 1 h56 kg_1406_496
    have h58 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 504 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 497 7 h57 kg_1406_497
    have h59 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 509 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 504 5 h58 kg_1406_504
    have h60 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 519 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 509 10 h59 kg_1406_509
    have h61 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 522 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 519 3 h60 kg_1406_519
    have h62 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 551 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 522 29 h61 kg_1406_522
    have h63 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 553 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 551 2 h62 kg_1406_551
    have h64 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 559 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 553 6 h63 kg_1406_553
    have h65 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 561 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 559 2 h64 kg_1406_559
    have h66 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 610 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 561 49 h65 kg_1406_561
    have h67 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 635 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 610 25 h66 kg_1406_610
    have h68 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 646 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 635 11 h67 kg_1406_635
    have h69 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 660 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 646 14 h68 kg_1406_646
    have h70 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 662 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 660 2 h69 kg_1406_660
    have h71 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 682 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 662 20 h70 kg_1406_662
    have h72 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 684 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 682 2 h71 kg_1406_682
    have h73 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 698 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 684 14 h72 kg_1406_684
    have h74 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 704 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 698 6 h73 kg_1406_698
    have h75 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 706 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 704 2 h74 kg_1406_704
    have h76 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 731 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 706 25 h75 kg_1406_706
    have h77 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 733 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 731 2 h76 kg_1406_731
    have h78 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 752 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 733 19 h77 kg_1406_733
    have h79 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 754 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 752 2 h78 kg_1406_752
    have h80 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 786 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 754 32 h79 kg_1406_754
    have h81 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 792 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 786 6 h80 kg_1406_786
    have h82 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 806 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 792 14 h81 kg_1406_792
    have h83 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 808 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 806 2 h82 kg_1406_806
    have h84 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 821 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 808 13 h83 kg_1406_808
    have h85 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 827 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 821 6 h84 kg_1406_821
    have h86 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 829 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 827 2 h85 kg_1406_827
    have h87 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 841 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 829 12 h86 kg_1406_829
    have h88 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 845 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 841 4 h87 kg_1406_841
    have h89 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 867 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 845 22 h88 kg_1406_845
    have h90 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 883 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 867 16 h89 kg_1406_867
    have h91 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 906 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 883 23 h90 kg_1406_883
    have h92 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 915 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 906 9 h91 kg_1406_906
    have h93 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 939 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 915 24 h92 kg_1406_915
    have h94 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 961 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 939 22 h93 kg_1406_939
    have h95 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 963 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 961 2 h94 kg_1406_961
    have h96 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 978 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 963 15 h95 kg_1406_963
    have h97 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 997 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 978 19 h96 kg_1406_978
    have h98 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1013 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 997 16 h97 kg_1406_997
    have h99 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1017 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1013 4 h98 kg_1406_1013
    have h100 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1050 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1017 33 h99 kg_1406_1017
    have h101 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1071 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1050 21 h100 kg_1406_1050
    have h102 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1073 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1071 2 h101 kg_1406_1071
    have h103 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1074 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1073 1 h102 kg_1406_1073
    have h104 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1075 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1074 1 h103 kg_1406_1074
    have h105 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1076 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1075 1 h104 kg_1406_1075
    have h106 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1077 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1076 1 h105 kg_1406_1076
    have h107 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1078 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1077 1 h106 kg_1406_1077
    have h108 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1080 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1078 2 h107 kg_1406_1078
    have h109 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1082 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1080 2 h108 kg_1406_1080
    have h110 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1084 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1082 2 h109 kg_1406_1082
    have h111 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1085 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1084 1 h110 kg_1406_1084
    have h112 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1087 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1085 2 h111 kg_1406_1085
    have h113 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1088 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1087 1 h112 kg_1406_1087
    have h114 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1093 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1088 5 h113 kg_1406_1088
    have h115 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1096 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1093 3 h114 kg_1406_1093
    have h116 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1097 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1096 1 h115 kg_1406_1096
    have h117 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1103 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1097 6 h116 kg_1406_1097
    have h118 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1104 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1103 1 h117 kg_1406_1103
    have h119 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1115 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1104 11 h118 kg_1406_1104
    have h120 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1118 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1115 3 h119 kg_1406_1115
    have h121 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1119 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1118 1 h120 kg_1406_1118
    have h122 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1122 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1119 3 h121 kg_1406_1119
    have h123 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1134 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1122 12 h122 kg_1406_1122
    have h124 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1136 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1134 2 h123 kg_1406_1134
    have h125 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1149 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1136 13 h124 kg_1406_1136
    have h126 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1155 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1149 6 h125 kg_1406_1149
    have h127 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1156 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1155 1 h126 kg_1406_1155
    have h128 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1171 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1156 15 h127 kg_1406_1156
    have h129 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1172 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1171 1 h128 kg_1406_1171
    have h130 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1205 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1172 33 h129 kg_1406_1172
    have h131 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1226 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1205 21 h130 kg_1406_1205
    have h132 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1258 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1226 32 h131 kg_1406_1226
    have h133 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1263 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1258 5 h132 kg_1406_1258
    have h134 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1287 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1263 24 h133 kg_1406_1263
    have h135 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1299 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1287 12 h134 kg_1406_1287
    have h136 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1330 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1299 31 h135 kg_1406_1299
    have h137 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1363 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1330 33 h136 kg_1406_1330
    have h138 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1371 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1363 8 h137 kg_1406_1363
    have h139 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1383 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1371 12 h138 kg_1406_1371
    have h140 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1439 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1383 56 h139 kg_1406_1383
    have h141 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1472 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1439 33 h140 kg_1406_1439
    have h142 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1485 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1472 13 h141 kg_1406_1472
    have h143 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1486 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1485 1 h142 kg_1406_1485
    have h144 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1487 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1486 1 h143 kg_1406_1486
    have h145 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1489 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1487 2 h144 kg_1406_1487
    have h146 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1493 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1489 4 h145 kg_1406_1489
    have h147 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1497 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1493 4 h146 kg_1406_1493
    have h148 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1498 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1497 1 h147 kg_1406_1497
    have h149 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1505 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1498 7 h148 kg_1406_1498
    have h150 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1507 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1505 2 h149 kg_1406_1505
    have h151 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1509 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1507 2 h150 kg_1406_1507
    have h152 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1510 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1509 1 h151 kg_1406_1509
    have h153 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1518 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1510 8 h152 kg_1406_1510
    have h154 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1535 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1518 17 h153 kg_1406_1518
    have h155 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1540 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1535 5 h154 kg_1406_1535
    have h156 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1560 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1540 20 h155 kg_1406_1540
    have h157 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1583 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1560 23 h156 kg_1406_1560
    have h158 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 0 1603 = true := IPChk.allR_join (Pts.glueIB K1406.lits KW_1406) 0 1583 20 h157 kg_1406_1583
    exact h158
  have hlen : K1406.lits.length = 1603 := by decide
  intro k h1 h2
  obtain rfl : k = 1406 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1406) K1406.lits KW_1406
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_288 : ∀ k, 1407 ≤ k → k < 1408 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2288 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 4 = true := kb_1407_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 4 3 h0 kb_1407_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 7 8 h1 kb_1407_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 15 8 h2 kb_1407_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 23 2 h3 kb_1407_23
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 25 1 h4 kb_1407_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 26 2 h5 kb_1407_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 28 1 h6 kb_1407_28
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 29 8 h7 kb_1407_29
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 37 14 h8 kb_1407_37
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 51 13 h9 kb_1407_51
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 64 4 h10 kb_1407_64
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 68 29 h11 kb_1407_68
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 97 2 h12 kb_1407_97
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 99 6 h13 kb_1407_99
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 105 2 h14 kb_1407_105
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 107 20 h15 kb_1407_107
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 127 1 h16 kb_1407_127
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 128 4 h17 kb_1407_128
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 132 6 h18 kb_1407_132
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 138 24 h19 kb_1407_138
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 162 1 h20 kb_1407_162
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 163 2 h21 kb_1407_163
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 165 1 h22 kb_1407_165
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 166 2 h23 kb_1407_166
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 168 1 h24 kb_1407_168
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 169 2 h25 kb_1407_169
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 171 29 h26 kb_1407_171
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 200 2 h27 kb_1407_200
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 202 6 h28 kb_1407_202
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 208 2 h29 kb_1407_208
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 210 22 h30 kb_1407_210
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 232 9 h31 kb_1407_232
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 241 57 h32 kb_1407_241
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 298 4 h33 kb_1407_298
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 302 1 h34 kb_1407_302
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 304 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 303 1 h35 kb_1407_303
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 304 13 h36 kb_1407_304
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 317 14 h37 kb_1407_317
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 331 6 h38 kb_1407_331
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 337 2 h39 kb_1407_337
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 339 18 h40 kb_1407_339
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 357 1 h41 kb_1407_357
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 358 2 h42 kb_1407_358
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 360 2 h43 kb_1407_360
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 386 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 362 24 h44 kb_1407_362
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 386 2 h45 kb_1407_386
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 394 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 388 6 h46 kb_1407_388
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 394 2 h47 kb_1407_394
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 396 16 h48 kb_1407_396
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 412 1 h49 kb_1407_412
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 413 3 h50 kb_1407_413
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 416 12 h51 kb_1407_416
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 428 4 h52 kb_1407_428
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 432 11 h53 kb_1407_432
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 458 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 443 15 h54 kb_1407_443
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 458 2 h55 kb_1407_458
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 460 14 h56 kb_1407_460
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 474 15 h57 kb_1407_474
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 489 16 h58 kb_1407_489
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 505 6 h59 kb_1407_505
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 513 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 511 2 h60 kb_1407_511
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 513 20 h61 kb_1407_513
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 533 7 h62 kb_1407_533
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 542 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 540 2 h63 kb_1407_540
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 542 20 h64 kb_1407_542
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 562 2 h65 kb_1407_562
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 564 20 h66 kb_1407_564
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 584 2 h67 kb_1407_584
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 605 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 586 19 h68 kb_1407_586
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 605 1 h69 kb_1407_605
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 606 3 h70 kb_1407_606
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 609 15 h71 kb_1407_609
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 624 10 h72 kb_1407_624
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 634 1 h73 kb_1407_634
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 635 29 h74 kb_1407_635
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 664 2 h75 kb_1407_664
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 666 6 h76 kb_1407_666
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 674 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 672 2 h77 kb_1407_672
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 674 22 h78 kb_1407_674
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 696 10 h79 kb_1407_696
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 765 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 706 59 h80 kb_1407_706
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 766 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 765 1 h81 kb_1407_765
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 766 1 h82 kb_1407_766
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 767 3 h83 kb_1407_767
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 774 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 770 4 h84 kb_1407_770
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 774 4 h85 kb_1407_774
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 778 8 h86 kb_1407_778
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 786 1 h87 kb_1407_786
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 787 2 h88 kb_1407_787
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 789 8 h89 kb_1407_789
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 797 7 h90 kb_1407_797
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 814 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 804 10 h91 kb_1407_804
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 814 9 h92 kb_1407_814
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 833 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 823 10 h93 kb_1407_823
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 835 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 833 2 h94 kb_1407_833
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 837 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 835 2 h95 kb_1407_835
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 843 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 837 6 h96 kb_1407_837
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 846 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 843 3 h97 kb_1407_843
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 846 9 h98 kb_1407_846
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 874 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 855 19 h99 kb_1407_855
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 876 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 874 2 h100 kb_1407_874
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 895 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 876 19 h101 kb_1407_876
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 901 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 895 6 h102 kb_1407_895
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 901 13 h103 kb_1407_901
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 914 6 h104 kb_1407_914
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 920 2 h105 kb_1407_920
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 941 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 922 19 h106 kb_1407_922
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 941 2 h107 kb_1407_941
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 956 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 943 13 h108 kb_1407_943
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 956 2 h109 kb_1407_956
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 958 14 h110 kb_1407_958
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 982 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 972 10 h111 kb_1407_972
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 988 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 982 6 h112 kb_1407_982
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 988 3 h113 kb_1407_988
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 991 5 h114 kb_1407_991
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 996 9 h115 kb_1407_996
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1005 8 h116 kb_1407_1005
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1015 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1013 2 h117 kb_1407_1013
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1027 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1015 12 h118 kb_1407_1015
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1034 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1027 7 h119 kb_1407_1027
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1036 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1034 2 h120 kb_1407_1034
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1048 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1036 12 h121 kb_1407_1036
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1051 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1048 3 h122 kb_1407_1048
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1057 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1051 6 h123 kb_1407_1051
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1059 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1057 2 h124 kb_1407_1057
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1059 13 h125 kb_1407_1059
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1074 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1072 2 h126 kb_1407_1072
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1074 8 h127 kb_1407_1074
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1094 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1082 12 h128 kb_1407_1082
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1096 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1094 2 h129 kb_1407_1094
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1096 13 h130 kb_1407_1096
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1109 1 h131 kb_1407_1109
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1110 5 h132 kb_1407_1110
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1115 12 h133 kb_1407_1115
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1127 3 h134 kb_1407_1127
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1130 18 h135 kb_1407_1130
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1148 6 h136 kb_1407_1148
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1154 6 h137 kb_1407_1154
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1160 6 h138 kb_1407_1160
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1166 14 h139 kb_1407_1166
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1180 4 h140 kb_1407_1180
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1184 2 h141 kb_1407_1184
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1186 21 h142 kb_1407_1186
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1207 17 h143 kb_1407_1207
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1224 8 h144 kb_1407_1224
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1232 17 h145 kb_1407_1232
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1249 20 h146 kb_1407_1249
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1269 32 h147 kb_1407_1269
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1301 2 h148 kb_1407_1301
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1303 14 h149 kb_1407_1303
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1317 30 h150 kb_1407_1317
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1347 55 h151 kb_1407_1347
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1402 1 h152 kb_1407_1402
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1403 1 h153 kb_1407_1403
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1404 2 h154 kb_1407_1404
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1406 1 h155 kb_1407_1406
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1407 3 h156 kb_1407_1407
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1410 1 h157 kb_1407_1410
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1411 1 h158 kb_1407_1411
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1412 3 h159 kb_1407_1412
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1415 3 h160 kb_1407_1415
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1418 2 h161 kb_1407_1418
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1420 29 h162 kb_1407_1420
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1449 2 h163 kb_1407_1449
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1451 6 h164 kb_1407_1451
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1457 10 h165 kb_1407_1457
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1467 77 h166 kb_1407_1467
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1544 4 h167 kb_1407_1544
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1548 14 h168 kb_1407_1548
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1562 13 h169 kb_1407_1562
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1575 1 h170 kb_1407_1575
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1577 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1576 1 h171 kb_1407_1576
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1577 1 h172 kb_1407_1577
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1578 1 h173 kb_1407_1578
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1579 1 h174 kb_1407_1579
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1580 9 h175 kb_1407_1580
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1589 24 h176 kb_1407_1589
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1619 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1613 6 h177 kb_1407_1613
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1623 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1619 4 h178 kb_1407_1619
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1623 65 h179 kb_1407_1623
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1688 4 h180 kb_1407_1688
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1692 4 h181 kb_1407_1692
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1696 21 h182 kb_1407_1696
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1736 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1717 19 h183 kb_1407_1717
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1748 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1736 12 h184 kb_1407_1736
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1773 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1748 25 h185 kb_1407_1748
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1773 2 h186 kb_1407_1773
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1775 8 h187 kb_1407_1775
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1800 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1783 17 h188 kb_1407_1783
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1800 18 h189 kb_1407_1800
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1847 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1818 29 h190 kb_1407_1818
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1849 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1847 2 h191 kb_1407_1847
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1849 6 h192 kb_1407_1849
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1857 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1855 2 h193 kb_1407_1855
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1879 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1857 22 h194 kb_1407_1857
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1925 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1879 46 h195 kb_1407_1879
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1930 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1925 5 h196 kb_1407_1925
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1931 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1930 1 h197 kb_1407_1930
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1931 12 h198 kb_1407_1931
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1956 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1943 13 h199 kb_1407_1943
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1956 9 h200 kb_1407_1956
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1973 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1965 8 h201 kb_1407_1965
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1988 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1973 15 h202 kb_1407_1973
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1988 3 h203 kb_1407_1988
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1991 5 h204 kb_1407_1991
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2006 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 1996 10 h205 kb_1407_1996
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2021 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2006 15 h206 kb_1407_2006
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2021 1 h207 kb_1407_2021
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2027 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2022 5 h208 kb_1407_2022
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2041 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2027 14 h209 kb_1407_2027
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2045 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2041 4 h210 kb_1407_2041
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2052 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2045 7 h211 kb_1407_2045
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2075 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2052 23 h212 kb_1407_2052
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2087 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2075 12 h213 kb_1407_2075
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2087 34 h214 kb_1407_2087
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2121 47 h215 kb_1407_2121
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2168 1 h216 kb_1407_2168
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2169 1 h217 kb_1407_2169
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2170 1 h218 kb_1407_2170
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2171 2 h219 kb_1407_2171
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2173 2 h220 kb_1407_2173
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2175 1 h221 kb_1407_2175
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2176 1 h222 kb_1407_2176
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2177 2 h223 kb_1407_2177
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2179 1 h224 kb_1407_2179
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2180 1 h225 kb_1407_2180
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2181 2 h226 kb_1407_2181
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2183 5 h227 kb_1407_2183
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2188 8 h228 kb_1407_2188
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2196 14 h229 kb_1407_2196
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2210 25 h230 kb_1407_2210
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2235 16 h231 kb_1407_2235
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2265 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2251 14 h232 kb_1407_2251
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1407.lits.getD i 0)) 0 2265 23 h233 kb_1407_2265
    exact h234
  have hg : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2288 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 4 = true := kg_1407_0
    have h1 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 7 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 4 3 h0 kg_1407_4
    have h2 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 15 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 7 8 h1 kg_1407_7
    have h3 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 23 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 15 8 h2 kg_1407_15
    have h4 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 25 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 23 2 h3 kg_1407_23
    have h5 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 26 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 25 1 h4 kg_1407_25
    have h6 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 28 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 26 2 h5 kg_1407_26
    have h7 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 29 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 28 1 h6 kg_1407_28
    have h8 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 37 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 29 8 h7 kg_1407_29
    have h9 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 51 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 37 14 h8 kg_1407_37
    have h10 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 64 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 51 13 h9 kg_1407_51
    have h11 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 68 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 64 4 h10 kg_1407_64
    have h12 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 97 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 68 29 h11 kg_1407_68
    have h13 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 99 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 97 2 h12 kg_1407_97
    have h14 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 105 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 99 6 h13 kg_1407_99
    have h15 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 107 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 105 2 h14 kg_1407_105
    have h16 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 127 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 107 20 h15 kg_1407_107
    have h17 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 128 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 127 1 h16 kg_1407_127
    have h18 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 132 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 128 4 h17 kg_1407_128
    have h19 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 138 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 132 6 h18 kg_1407_132
    have h20 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 162 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 138 24 h19 kg_1407_138
    have h21 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 163 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 162 1 h20 kg_1407_162
    have h22 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 165 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 163 2 h21 kg_1407_163
    have h23 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 166 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 165 1 h22 kg_1407_165
    have h24 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 168 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 166 2 h23 kg_1407_166
    have h25 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 169 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 168 1 h24 kg_1407_168
    have h26 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 171 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 169 2 h25 kg_1407_169
    have h27 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 200 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 171 29 h26 kg_1407_171
    have h28 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 202 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 200 2 h27 kg_1407_200
    have h29 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 208 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 202 6 h28 kg_1407_202
    have h30 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 210 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 208 2 h29 kg_1407_208
    have h31 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 232 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 210 22 h30 kg_1407_210
    have h32 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 241 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 232 9 h31 kg_1407_232
    have h33 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 298 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 241 57 h32 kg_1407_241
    have h34 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 302 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 298 4 h33 kg_1407_298
    have h35 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 303 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 302 1 h34 kg_1407_302
    have h36 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 304 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 303 1 h35 kg_1407_303
    have h37 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 317 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 304 13 h36 kg_1407_304
    have h38 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 331 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 317 14 h37 kg_1407_317
    have h39 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 337 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 331 6 h38 kg_1407_331
    have h40 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 339 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 337 2 h39 kg_1407_337
    have h41 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 357 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 339 18 h40 kg_1407_339
    have h42 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 358 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 357 1 h41 kg_1407_357
    have h43 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 360 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 358 2 h42 kg_1407_358
    have h44 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 362 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 360 2 h43 kg_1407_360
    have h45 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 386 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 362 24 h44 kg_1407_362
    have h46 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 388 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 386 2 h45 kg_1407_386
    have h47 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 394 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 388 6 h46 kg_1407_388
    have h48 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 396 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 394 2 h47 kg_1407_394
    have h49 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 412 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 396 16 h48 kg_1407_396
    have h50 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 413 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 412 1 h49 kg_1407_412
    have h51 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 416 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 413 3 h50 kg_1407_413
    have h52 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 428 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 416 12 h51 kg_1407_416
    have h53 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 432 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 428 4 h52 kg_1407_428
    have h54 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 443 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 432 11 h53 kg_1407_432
    have h55 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 458 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 443 15 h54 kg_1407_443
    have h56 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 460 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 458 2 h55 kg_1407_458
    have h57 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 474 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 460 14 h56 kg_1407_460
    have h58 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 489 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 474 15 h57 kg_1407_474
    have h59 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 505 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 489 16 h58 kg_1407_489
    have h60 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 511 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 505 6 h59 kg_1407_505
    have h61 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 513 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 511 2 h60 kg_1407_511
    have h62 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 533 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 513 20 h61 kg_1407_513
    have h63 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 540 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 533 7 h62 kg_1407_533
    have h64 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 542 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 540 2 h63 kg_1407_540
    have h65 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 562 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 542 20 h64 kg_1407_542
    have h66 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 564 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 562 2 h65 kg_1407_562
    have h67 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 584 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 564 20 h66 kg_1407_564
    have h68 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 586 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 584 2 h67 kg_1407_584
    have h69 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 605 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 586 19 h68 kg_1407_586
    have h70 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 606 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 605 1 h69 kg_1407_605
    have h71 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 609 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 606 3 h70 kg_1407_606
    have h72 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 624 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 609 15 h71 kg_1407_609
    have h73 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 634 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 624 10 h72 kg_1407_624
    have h74 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 635 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 634 1 h73 kg_1407_634
    have h75 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 664 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 635 29 h74 kg_1407_635
    have h76 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 666 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 664 2 h75 kg_1407_664
    have h77 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 672 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 666 6 h76 kg_1407_666
    have h78 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 674 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 672 2 h77 kg_1407_672
    have h79 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 696 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 674 22 h78 kg_1407_674
    have h80 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 706 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 696 10 h79 kg_1407_696
    have h81 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 765 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 706 59 h80 kg_1407_706
    have h82 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 766 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 765 1 h81 kg_1407_765
    have h83 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 767 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 766 1 h82 kg_1407_766
    have h84 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 770 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 767 3 h83 kg_1407_767
    have h85 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 774 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 770 4 h84 kg_1407_770
    have h86 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 778 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 774 4 h85 kg_1407_774
    have h87 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 786 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 778 8 h86 kg_1407_778
    have h88 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 787 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 786 1 h87 kg_1407_786
    have h89 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 789 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 787 2 h88 kg_1407_787
    have h90 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 797 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 789 8 h89 kg_1407_789
    have h91 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 804 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 797 7 h90 kg_1407_797
    have h92 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 814 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 804 10 h91 kg_1407_804
    have h93 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 823 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 814 9 h92 kg_1407_814
    have h94 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 833 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 823 10 h93 kg_1407_823
    have h95 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 835 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 833 2 h94 kg_1407_833
    have h96 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 837 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 835 2 h95 kg_1407_835
    have h97 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 843 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 837 6 h96 kg_1407_837
    have h98 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 846 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 843 3 h97 kg_1407_843
    have h99 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 855 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 846 9 h98 kg_1407_846
    have h100 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 874 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 855 19 h99 kg_1407_855
    have h101 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 876 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 874 2 h100 kg_1407_874
    have h102 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 895 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 876 19 h101 kg_1407_876
    have h103 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 901 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 895 6 h102 kg_1407_895
    have h104 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 914 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 901 13 h103 kg_1407_901
    have h105 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 920 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 914 6 h104 kg_1407_914
    have h106 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 922 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 920 2 h105 kg_1407_920
    have h107 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 941 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 922 19 h106 kg_1407_922
    have h108 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 943 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 941 2 h107 kg_1407_941
    have h109 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 956 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 943 13 h108 kg_1407_943
    have h110 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 958 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 956 2 h109 kg_1407_956
    have h111 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 972 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 958 14 h110 kg_1407_958
    have h112 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 982 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 972 10 h111 kg_1407_972
    have h113 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 988 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 982 6 h112 kg_1407_982
    have h114 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 991 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 988 3 h113 kg_1407_988
    have h115 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 996 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 991 5 h114 kg_1407_991
    have h116 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1005 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 996 9 h115 kg_1407_996
    have h117 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1013 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1005 8 h116 kg_1407_1005
    have h118 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1015 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1013 2 h117 kg_1407_1013
    have h119 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1027 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1015 12 h118 kg_1407_1015
    have h120 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1034 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1027 7 h119 kg_1407_1027
    have h121 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1036 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1034 2 h120 kg_1407_1034
    have h122 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1048 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1036 12 h121 kg_1407_1036
    have h123 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1051 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1048 3 h122 kg_1407_1048
    have h124 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1057 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1051 6 h123 kg_1407_1051
    have h125 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1059 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1057 2 h124 kg_1407_1057
    have h126 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1072 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1059 13 h125 kg_1407_1059
    have h127 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1074 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1072 2 h126 kg_1407_1072
    have h128 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1082 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1074 8 h127 kg_1407_1074
    have h129 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1094 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1082 12 h128 kg_1407_1082
    have h130 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1096 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1094 2 h129 kg_1407_1094
    have h131 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1109 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1096 13 h130 kg_1407_1096
    have h132 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1110 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1109 1 h131 kg_1407_1109
    have h133 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1115 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1110 5 h132 kg_1407_1110
    have h134 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1127 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1115 12 h133 kg_1407_1115
    have h135 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1130 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1127 3 h134 kg_1407_1127
    have h136 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1148 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1130 18 h135 kg_1407_1130
    have h137 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1154 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1148 6 h136 kg_1407_1148
    have h138 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1160 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1154 6 h137 kg_1407_1154
    have h139 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1166 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1160 6 h138 kg_1407_1160
    have h140 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1180 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1166 14 h139 kg_1407_1166
    have h141 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1184 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1180 4 h140 kg_1407_1180
    have h142 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1186 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1184 2 h141 kg_1407_1184
    have h143 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1207 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1186 21 h142 kg_1407_1186
    have h144 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1224 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1207 17 h143 kg_1407_1207
    have h145 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1232 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1224 8 h144 kg_1407_1224
    have h146 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1249 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1232 17 h145 kg_1407_1232
    have h147 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1269 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1249 20 h146 kg_1407_1249
    have h148 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1301 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1269 32 h147 kg_1407_1269
    have h149 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1303 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1301 2 h148 kg_1407_1301
    have h150 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1317 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1303 14 h149 kg_1407_1303
    have h151 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1347 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1317 30 h150 kg_1407_1317
    have h152 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1402 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1347 55 h151 kg_1407_1347
    have h153 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1403 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1402 1 h152 kg_1407_1402
    have h154 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1404 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1403 1 h153 kg_1407_1403
    have h155 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1406 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1404 2 h154 kg_1407_1404
    have h156 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1407 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1406 1 h155 kg_1407_1406
    have h157 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1410 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1407 3 h156 kg_1407_1407
    have h158 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1411 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1410 1 h157 kg_1407_1410
    have h159 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1412 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1411 1 h158 kg_1407_1411
    have h160 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1415 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1412 3 h159 kg_1407_1412
    have h161 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1418 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1415 3 h160 kg_1407_1415
    have h162 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1420 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1418 2 h161 kg_1407_1418
    have h163 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1449 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1420 29 h162 kg_1407_1420
    have h164 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1451 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1449 2 h163 kg_1407_1449
    have h165 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1457 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1451 6 h164 kg_1407_1451
    have h166 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1467 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1457 10 h165 kg_1407_1457
    have h167 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1544 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1467 77 h166 kg_1407_1467
    have h168 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1548 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1544 4 h167 kg_1407_1544
    have h169 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1562 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1548 14 h168 kg_1407_1548
    have h170 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1575 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1562 13 h169 kg_1407_1562
    have h171 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1576 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1575 1 h170 kg_1407_1575
    have h172 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1577 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1576 1 h171 kg_1407_1576
    have h173 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1578 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1577 1 h172 kg_1407_1577
    have h174 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1579 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1578 1 h173 kg_1407_1578
    have h175 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1580 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1579 1 h174 kg_1407_1579
    have h176 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1589 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1580 9 h175 kg_1407_1580
    have h177 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1613 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1589 24 h176 kg_1407_1589
    have h178 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1619 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1613 6 h177 kg_1407_1613
    have h179 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1623 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1619 4 h178 kg_1407_1619
    have h180 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1688 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1623 65 h179 kg_1407_1623
    have h181 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1692 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1688 4 h180 kg_1407_1688
    have h182 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1696 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1692 4 h181 kg_1407_1692
    have h183 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1717 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1696 21 h182 kg_1407_1696
    have h184 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1736 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1717 19 h183 kg_1407_1717
    have h185 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1748 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1736 12 h184 kg_1407_1736
    have h186 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1773 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1748 25 h185 kg_1407_1748
    have h187 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1775 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1773 2 h186 kg_1407_1773
    have h188 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1783 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1775 8 h187 kg_1407_1775
    have h189 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1800 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1783 17 h188 kg_1407_1783
    have h190 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1818 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1800 18 h189 kg_1407_1800
    have h191 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1847 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1818 29 h190 kg_1407_1818
    have h192 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1849 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1847 2 h191 kg_1407_1847
    have h193 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1855 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1849 6 h192 kg_1407_1849
    have h194 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1857 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1855 2 h193 kg_1407_1855
    have h195 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1879 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1857 22 h194 kg_1407_1857
    have h196 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1925 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1879 46 h195 kg_1407_1879
    have h197 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1930 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1925 5 h196 kg_1407_1925
    have h198 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1931 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1930 1 h197 kg_1407_1930
    have h199 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1943 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1931 12 h198 kg_1407_1931
    have h200 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1956 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1943 13 h199 kg_1407_1943
    have h201 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1965 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1956 9 h200 kg_1407_1956
    have h202 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1973 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1965 8 h201 kg_1407_1965
    have h203 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1988 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1973 15 h202 kg_1407_1973
    have h204 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1991 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1988 3 h203 kg_1407_1988
    have h205 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 1996 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1991 5 h204 kg_1407_1991
    have h206 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2006 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 1996 10 h205 kg_1407_1996
    have h207 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2021 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2006 15 h206 kg_1407_2006
    have h208 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2022 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2021 1 h207 kg_1407_2021
    have h209 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2027 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2022 5 h208 kg_1407_2022
    have h210 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2041 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2027 14 h209 kg_1407_2027
    have h211 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2045 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2041 4 h210 kg_1407_2041
    have h212 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2052 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2045 7 h211 kg_1407_2045
    have h213 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2075 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2052 23 h212 kg_1407_2052
    have h214 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2087 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2075 12 h213 kg_1407_2075
    have h215 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2121 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2087 34 h214 kg_1407_2087
    have h216 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2168 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2121 47 h215 kg_1407_2121
    have h217 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2169 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2168 1 h216 kg_1407_2168
    have h218 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2170 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2169 1 h217 kg_1407_2169
    have h219 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2171 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2170 1 h218 kg_1407_2170
    have h220 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2173 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2171 2 h219 kg_1407_2171
    have h221 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2175 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2173 2 h220 kg_1407_2173
    have h222 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2176 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2175 1 h221 kg_1407_2175
    have h223 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2177 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2176 1 h222 kg_1407_2176
    have h224 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2179 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2177 2 h223 kg_1407_2177
    have h225 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2180 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2179 1 h224 kg_1407_2179
    have h226 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2181 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2180 1 h225 kg_1407_2180
    have h227 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2183 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2181 2 h226 kg_1407_2181
    have h228 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2188 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2183 5 h227 kg_1407_2183
    have h229 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2196 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2188 8 h228 kg_1407_2188
    have h230 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2210 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2196 14 h229 kg_1407_2196
    have h231 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2235 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2210 25 h230 kg_1407_2210
    have h232 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2251 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2235 16 h231 kg_1407_2235
    have h233 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2265 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2251 14 h232 kg_1407_2251
    have h234 : IPChk.allR (Pts.glueIB K1407.lits KW_1407) 0 2288 = true := IPChk.allR_join (Pts.glueIB K1407.lits KW_1407) 0 2265 23 h233 kg_1407_2265
    exact h234
  have hlen : K1407.lits.length = 2288 := by decide
  intro k h1 h2
  obtain rfl : k = 1407 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1407) K1407.lits KW_1407
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_289 : ∀ k, 1408 ≤ k → k < 1409 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1408 JW_1408 1408 1 jr_1408
theorem jr6_290 : ∀ k, 1409 ≤ k → k < 1410 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 1065 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 4 = true := kb_1409_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 4 3 h0 kb_1409_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 7 15 h1 kb_1409_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 22 2 h2 kb_1409_22
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 24 14 h3 kb_1409_24
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 38 2 h4 kb_1409_38
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 40 1 h5 kb_1409_40
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 41 9 h6 kb_1409_41
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 50 1 h7 kb_1409_50
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 51 17 h8 kb_1409_51
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 68 14 h9 kb_1409_68
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 82 6 h10 kb_1409_82
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 88 2 h11 kb_1409_88
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 90 22 h12 kb_1409_90
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 112 2 h13 kb_1409_112
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 114 3 h14 kb_1409_114
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 117 27 h15 kb_1409_117
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 144 4 h16 kb_1409_144
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 148 1 h17 kb_1409_148
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 149 1 h18 kb_1409_149
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 150 35 h19 kb_1409_150
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 185 10 h20 kb_1409_185
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 195 54 h21 kb_1409_195
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 249 73 h22 kb_1409_249
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 322 12 h23 kb_1409_322
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 334 4 h24 kb_1409_334
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 338 12 h25 kb_1409_338
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 350 14 h26 kb_1409_350
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 364 2 h27 kb_1409_364
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 366 14 h28 kb_1409_366
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 380 15 h29 kb_1409_380
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 395 22 h30 kb_1409_395
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 417 25 h31 kb_1409_417
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 442 24 h32 kb_1409_442
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 466 30 h33 kb_1409_466
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 496 9 h34 kb_1409_496
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 505 2 h35 kb_1409_505
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 507 18 h36 kb_1409_507
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 526 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 525 1 h37 kb_1409_525
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 574 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 526 48 h38 kb_1409_526
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 574 1 h39 kb_1409_574
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 575 41 h40 kb_1409_575
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 616 2 h41 kb_1409_616
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 618 6 h42 kb_1409_618
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 624 5 h43 kb_1409_624
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 629 15 h44 kb_1409_629
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 644 33 h45 kb_1409_644
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 677 30 h46 kb_1409_677
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 707 34 h47 kb_1409_707
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 741 57 h48 kb_1409_741
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 889 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 798 91 h49 kb_1409_798
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 889 83 h50 kb_1409_889
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 972 56 h51 kb_1409_972
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 1065 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1409.lits.getD i 0)) 0 1028 37 h52 kb_1409_1028
    exact h53
  have hg : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 1065 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 4 = true := kg_1409_0
    have h1 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 7 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 4 3 h0 kg_1409_4
    have h2 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 22 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 7 15 h1 kg_1409_7
    have h3 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 24 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 22 2 h2 kg_1409_22
    have h4 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 38 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 24 14 h3 kg_1409_24
    have h5 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 40 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 38 2 h4 kg_1409_38
    have h6 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 41 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 40 1 h5 kg_1409_40
    have h7 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 50 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 41 9 h6 kg_1409_41
    have h8 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 51 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 50 1 h7 kg_1409_50
    have h9 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 68 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 51 17 h8 kg_1409_51
    have h10 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 82 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 68 14 h9 kg_1409_68
    have h11 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 88 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 82 6 h10 kg_1409_82
    have h12 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 90 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 88 2 h11 kg_1409_88
    have h13 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 112 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 90 22 h12 kg_1409_90
    have h14 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 114 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 112 2 h13 kg_1409_112
    have h15 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 117 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 114 3 h14 kg_1409_114
    have h16 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 144 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 117 27 h15 kg_1409_117
    have h17 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 148 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 144 4 h16 kg_1409_144
    have h18 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 149 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 148 1 h17 kg_1409_148
    have h19 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 150 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 149 1 h18 kg_1409_149
    have h20 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 185 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 150 35 h19 kg_1409_150
    have h21 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 195 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 185 10 h20 kg_1409_185
    have h22 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 249 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 195 54 h21 kg_1409_195
    have h23 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 322 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 249 73 h22 kg_1409_249
    have h24 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 334 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 322 12 h23 kg_1409_322
    have h25 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 338 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 334 4 h24 kg_1409_334
    have h26 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 350 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 338 12 h25 kg_1409_338
    have h27 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 364 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 350 14 h26 kg_1409_350
    have h28 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 366 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 364 2 h27 kg_1409_364
    have h29 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 380 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 366 14 h28 kg_1409_366
    have h30 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 395 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 380 15 h29 kg_1409_380
    have h31 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 417 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 395 22 h30 kg_1409_395
    have h32 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 442 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 417 25 h31 kg_1409_417
    have h33 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 466 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 442 24 h32 kg_1409_442
    have h34 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 496 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 466 30 h33 kg_1409_466
    have h35 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 505 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 496 9 h34 kg_1409_496
    have h36 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 507 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 505 2 h35 kg_1409_505
    have h37 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 525 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 507 18 h36 kg_1409_507
    have h38 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 526 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 525 1 h37 kg_1409_525
    have h39 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 574 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 526 48 h38 kg_1409_526
    have h40 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 575 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 574 1 h39 kg_1409_574
    have h41 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 616 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 575 41 h40 kg_1409_575
    have h42 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 618 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 616 2 h41 kg_1409_616
    have h43 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 624 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 618 6 h42 kg_1409_618
    have h44 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 629 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 624 5 h43 kg_1409_624
    have h45 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 644 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 629 15 h44 kg_1409_629
    have h46 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 677 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 644 33 h45 kg_1409_644
    have h47 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 707 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 677 30 h46 kg_1409_677
    have h48 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 741 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 707 34 h47 kg_1409_707
    have h49 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 798 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 741 57 h48 kg_1409_741
    have h50 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 889 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 798 91 h49 kg_1409_798
    have h51 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 972 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 889 83 h50 kg_1409_889
    have h52 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 1028 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 972 56 h51 kg_1409_972
    have h53 : IPChk.allR (Pts.glueIB K1409.lits KW_1409) 0 1065 = true := IPChk.allR_join (Pts.glueIB K1409.lits KW_1409) 0 1028 37 h52 kg_1409_1028
    exact h53
  have hlen : K1409.lits.length = 1065 := by decide
  intro k h1 h2
  obtain rfl : k = 1409 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1409) K1409.lits KW_1409
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_291 : ∀ k, 1410 ≤ k → k < 1412 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1410 JW_1410 1410 2 jr_1410
theorem jr6_292 : ∀ k, 1412 ≤ k → k < 1413 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 371 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 3 = true := kb_1412_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 3 15 h0 kb_1412_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 18 7 h1 kb_1412_18
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 25 1 h2 kb_1412_25
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 26 13 h3 kb_1412_26
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 39 43 h4 kb_1412_39
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 82 14 h5 kb_1412_82
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 96 6 h6 kb_1412_96
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 102 10 h7 kb_1412_102
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 112 20 h8 kb_1412_112
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 132 45 h9 kb_1412_132
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 177 12 h10 kb_1412_177
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 189 47 h11 kb_1412_189
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 236 60 h12 kb_1412_236
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 296 4 h13 kb_1412_296
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 300 2 h14 kb_1412_300
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 324 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 302 22 h15 kb_1412_302
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1412.lits.getD i 0)) 0 324 47 h16 kb_1412_324
    exact h17
  have hg : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 371 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 3 = true := kg_1412_0
    have h1 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 18 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 3 15 h0 kg_1412_3
    have h2 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 25 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 18 7 h1 kg_1412_18
    have h3 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 26 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 25 1 h2 kg_1412_25
    have h4 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 39 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 26 13 h3 kg_1412_26
    have h5 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 82 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 39 43 h4 kg_1412_39
    have h6 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 96 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 82 14 h5 kg_1412_82
    have h7 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 102 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 96 6 h6 kg_1412_96
    have h8 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 112 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 102 10 h7 kg_1412_102
    have h9 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 132 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 112 20 h8 kg_1412_112
    have h10 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 177 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 132 45 h9 kg_1412_132
    have h11 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 189 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 177 12 h10 kg_1412_177
    have h12 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 236 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 189 47 h11 kg_1412_189
    have h13 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 296 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 236 60 h12 kg_1412_236
    have h14 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 300 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 296 4 h13 kg_1412_296
    have h15 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 302 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 300 2 h14 kg_1412_300
    have h16 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 324 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 302 22 h15 kg_1412_302
    have h17 : IPChk.allR (Pts.glueIB K1412.lits KW_1412) 0 371 = true := IPChk.allR_join (Pts.glueIB K1412.lits KW_1412) 0 324 47 h16 kg_1412_324
    exact h17
  have hlen : K1412.lits.length = 371 := by decide
  intro k h1 h2
  obtain rfl : k = 1412 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1412) K1412.lits KW_1412
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_293 : ∀ k, 1413 ≤ k → k < 1414 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 433 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 5 = true := kb_1413_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 5 14 h0 kb_1413_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 19 1 h1 kb_1413_19
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 20 18 h2 kb_1413_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 38 39 h3 kb_1413_38
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 77 12 h4 kb_1413_77
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 89 4 h5 kb_1413_89
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 93 11 h6 kb_1413_93
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 104 15 h7 kb_1413_104
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 119 2 h8 kb_1413_119
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 121 14 h9 kb_1413_121
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 135 14 h10 kb_1413_135
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 149 2 h11 kb_1413_149
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 151 15 h12 kb_1413_151
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 166 21 h13 kb_1413_166
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 187 6 h14 kb_1413_187
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 193 2 h15 kb_1413_193
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 195 17 h16 kb_1413_195
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 212 2 h17 kb_1413_212
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 214 4 h18 kb_1413_214
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 218 2 h19 kb_1413_218
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 220 21 h20 kb_1413_220
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 241 28 h21 kb_1413_241
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 269 15 h22 kb_1413_269
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 284 27 h23 kb_1413_284
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 311 19 h24 kb_1413_311
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 330 33 h25 kb_1413_330
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 363 9 h26 kb_1413_363
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 372 58 h27 kb_1413_372
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1413.lits.getD i 0)) 0 430 3 h28 kb_1413_430
    exact h29
  have hg : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 433 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 5 = true := kg_1413_0
    have h1 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 19 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 5 14 h0 kg_1413_5
    have h2 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 20 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 19 1 h1 kg_1413_19
    have h3 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 38 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 20 18 h2 kg_1413_20
    have h4 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 77 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 38 39 h3 kg_1413_38
    have h5 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 89 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 77 12 h4 kg_1413_77
    have h6 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 93 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 89 4 h5 kg_1413_89
    have h7 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 104 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 93 11 h6 kg_1413_93
    have h8 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 119 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 104 15 h7 kg_1413_104
    have h9 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 121 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 119 2 h8 kg_1413_119
    have h10 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 135 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 121 14 h9 kg_1413_121
    have h11 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 149 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 135 14 h10 kg_1413_135
    have h12 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 151 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 149 2 h11 kg_1413_149
    have h13 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 166 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 151 15 h12 kg_1413_151
    have h14 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 187 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 166 21 h13 kg_1413_166
    have h15 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 193 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 187 6 h14 kg_1413_187
    have h16 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 195 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 193 2 h15 kg_1413_193
    have h17 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 212 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 195 17 h16 kg_1413_195
    have h18 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 214 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 212 2 h17 kg_1413_212
    have h19 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 218 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 214 4 h18 kg_1413_214
    have h20 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 220 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 218 2 h19 kg_1413_218
    have h21 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 241 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 220 21 h20 kg_1413_220
    have h22 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 269 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 241 28 h21 kg_1413_241
    have h23 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 284 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 269 15 h22 kg_1413_269
    have h24 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 311 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 284 27 h23 kg_1413_284
    have h25 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 330 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 311 19 h24 kg_1413_311
    have h26 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 363 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 330 33 h25 kg_1413_330
    have h27 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 372 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 363 9 h26 kg_1413_363
    have h28 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 430 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 372 58 h27 kg_1413_372
    have h29 : IPChk.allR (Pts.glueIB K1413.lits KW_1413) 0 433 = true := IPChk.allR_join (Pts.glueIB K1413.lits KW_1413) 0 430 3 h28 kg_1413_430
    exact h29
  have hlen : K1413.lits.length = 433 := by decide
  intro k h1 h2
  obtain rfl : k = 1413 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1413) K1413.lits KW_1413
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_294 : ∀ k, 1414 ≤ k → k < 1415 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1414 JW_1414 1414 1 jr_1414
theorem jr6_295 : ∀ k, 1415 ≤ k → k < 1416 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 802 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 1 = true := kb_1415_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 1 2 h0 kb_1415_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 3 13 h1 kb_1415_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 16 18 h2 kb_1415_16
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 34 6 h3 kb_1415_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 40 2 h4 kb_1415_40
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 42 22 h5 kb_1415_42
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 64 2 h6 kb_1415_64
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 66 6 h7 kb_1415_66
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 72 12 h8 kb_1415_72
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 84 4 h9 kb_1415_84
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 88 12 h10 kb_1415_88
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 100 15 h11 kb_1415_100
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 115 2 h12 kb_1415_115
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 117 14 h13 kb_1415_117
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 131 15 h14 kb_1415_131
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 146 2 h15 kb_1415_146
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 148 15 h16 kb_1415_148
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 163 6 h17 kb_1415_163
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 169 2 h18 kb_1415_169
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 171 22 h19 kb_1415_171
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 193 8 h20 kb_1415_193
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 201 2 h21 kb_1415_201
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 203 22 h22 kb_1415_203
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 225 3 h23 kb_1415_225
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 228 22 h24 kb_1415_228
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 250 1 h25 kb_1415_250
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 251 4 h26 kb_1415_251
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 255 20 h27 kb_1415_255
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 275 2 h28 kb_1415_275
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 277 1 h29 kb_1415_277
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 278 1 h30 kb_1415_278
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 279 2 h31 kb_1415_279
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 281 18 h32 kb_1415_281
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 299 8 h33 kb_1415_299
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 307 6 h34 kb_1415_307
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 313 21 h35 kb_1415_313
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 334 4 h36 kb_1415_334
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 338 2 h37 kb_1415_338
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 340 23 h38 kb_1415_340
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 363 21 h39 kb_1415_363
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 384 8 h40 kb_1415_384
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 392 18 h41 kb_1415_392
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 410 12 h42 kb_1415_410
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 422 17 h43 kb_1415_422
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 439 4 h44 kb_1415_439
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 443 5 h45 kb_1415_443
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 448 35 h46 kb_1415_448
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 483 19 h47 kb_1415_483
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 502 15 h48 kb_1415_502
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 517 31 h49 kb_1415_517
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 548 10 h50 kb_1415_548
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 558 3 h51 kb_1415_558
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 592 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 561 31 h52 kb_1415_561
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 617 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 592 25 h53 kb_1415_592
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 617 26 h54 kb_1415_617
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 643 35 h55 kb_1415_643
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 678 62 h56 kb_1415_678
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 740 35 h57 kb_1415_740
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1415.lits.getD i 0)) 0 775 27 h58 kb_1415_775
    exact h59
  have hg : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 802 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 1 = true := kg_1415_0
    have h1 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 3 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 1 2 h0 kg_1415_1
    have h2 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 16 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 3 13 h1 kg_1415_3
    have h3 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 34 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 16 18 h2 kg_1415_16
    have h4 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 40 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 34 6 h3 kg_1415_34
    have h5 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 42 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 40 2 h4 kg_1415_40
    have h6 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 64 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 42 22 h5 kg_1415_42
    have h7 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 66 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 64 2 h6 kg_1415_64
    have h8 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 72 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 66 6 h7 kg_1415_66
    have h9 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 84 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 72 12 h8 kg_1415_72
    have h10 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 88 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 84 4 h9 kg_1415_84
    have h11 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 100 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 88 12 h10 kg_1415_88
    have h12 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 115 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 100 15 h11 kg_1415_100
    have h13 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 117 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 115 2 h12 kg_1415_115
    have h14 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 131 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 117 14 h13 kg_1415_117
    have h15 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 146 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 131 15 h14 kg_1415_131
    have h16 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 148 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 146 2 h15 kg_1415_146
    have h17 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 163 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 148 15 h16 kg_1415_148
    have h18 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 169 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 163 6 h17 kg_1415_163
    have h19 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 171 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 169 2 h18 kg_1415_169
    have h20 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 193 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 171 22 h19 kg_1415_171
    have h21 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 201 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 193 8 h20 kg_1415_193
    have h22 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 203 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 201 2 h21 kg_1415_201
    have h23 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 225 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 203 22 h22 kg_1415_203
    have h24 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 228 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 225 3 h23 kg_1415_225
    have h25 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 250 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 228 22 h24 kg_1415_228
    have h26 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 251 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 250 1 h25 kg_1415_250
    have h27 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 255 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 251 4 h26 kg_1415_251
    have h28 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 275 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 255 20 h27 kg_1415_255
    have h29 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 277 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 275 2 h28 kg_1415_275
    have h30 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 278 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 277 1 h29 kg_1415_277
    have h31 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 279 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 278 1 h30 kg_1415_278
    have h32 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 281 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 279 2 h31 kg_1415_279
    have h33 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 299 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 281 18 h32 kg_1415_281
    have h34 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 307 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 299 8 h33 kg_1415_299
    have h35 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 313 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 307 6 h34 kg_1415_307
    have h36 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 334 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 313 21 h35 kg_1415_313
    have h37 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 338 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 334 4 h36 kg_1415_334
    have h38 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 340 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 338 2 h37 kg_1415_338
    have h39 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 363 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 340 23 h38 kg_1415_340
    have h40 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 384 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 363 21 h39 kg_1415_363
    have h41 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 392 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 384 8 h40 kg_1415_384
    have h42 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 410 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 392 18 h41 kg_1415_392
    have h43 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 422 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 410 12 h42 kg_1415_410
    have h44 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 439 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 422 17 h43 kg_1415_422
    have h45 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 443 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 439 4 h44 kg_1415_439
    have h46 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 448 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 443 5 h45 kg_1415_443
    have h47 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 483 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 448 35 h46 kg_1415_448
    have h48 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 502 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 483 19 h47 kg_1415_483
    have h49 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 517 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 502 15 h48 kg_1415_502
    have h50 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 548 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 517 31 h49 kg_1415_517
    have h51 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 558 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 548 10 h50 kg_1415_548
    have h52 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 561 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 558 3 h51 kg_1415_558
    have h53 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 592 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 561 31 h52 kg_1415_561
    have h54 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 617 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 592 25 h53 kg_1415_592
    have h55 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 643 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 617 26 h54 kg_1415_617
    have h56 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 678 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 643 35 h55 kg_1415_643
    have h57 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 740 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 678 62 h56 kg_1415_678
    have h58 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 775 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 740 35 h57 kg_1415_740
    have h59 : IPChk.allR (Pts.glueIB K1415.lits KW_1415) 0 802 = true := IPChk.allR_join (Pts.glueIB K1415.lits KW_1415) 0 775 27 h58 kg_1415_775
    exact h59
  have hlen : K1415.lits.length = 802 := by decide
  intro k h1 h2
  obtain rfl : k = 1415 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1415) K1415.lits KW_1415
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_296 : ∀ k, 1416 ≤ k → k < 1459 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1416 JW_1416 1416 43 jr_1416
theorem jr6_297 : ∀ k, 1459 ≤ k → k < 1460 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 837 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 4 = true := kb_1459_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 4 1 h0 kb_1459_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 5 13 h1 kb_1459_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 18 1 h2 kb_1459_18
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 19 9 h3 kb_1459_19
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 28 1 h4 kb_1459_28
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 29 1 h5 kb_1459_29
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 30 18 h6 kb_1459_30
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 48 107 h7 kb_1459_48
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 155 12 h8 kb_1459_155
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 167 4 h9 kb_1459_167
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 171 28 h10 kb_1459_171
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 199 6 h11 kb_1459_199
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 205 2 h12 kb_1459_205
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 207 21 h13 kb_1459_207
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 228 10 h14 kb_1459_228
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 238 34 h15 kb_1459_238
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 272 36 h16 kb_1459_272
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 308 2 h17 kb_1459_308
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 310 1 h18 kb_1459_310
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 311 7 h19 kb_1459_311
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 324 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 318 6 h20 kb_1459_318
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 324 20 h21 kb_1459_324
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 346 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 344 2 h22 kb_1459_344
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 346 10 h23 kb_1459_346
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 356 1 h24 kb_1459_356
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 357 1 h25 kb_1459_357
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 358 2 h26 kb_1459_358
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 360 3 h27 kb_1459_360
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 363 2 h28 kb_1459_363
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 365 2 h29 kb_1459_365
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 367 8 h30 kb_1459_367
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 375 3 h31 kb_1459_375
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 378 2 h32 kb_1459_378
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 380 7 h33 kb_1459_380
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 390 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 387 3 h34 kb_1459_387
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 394 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 390 4 h35 kb_1459_390
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 394 1 h36 kb_1459_394
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 400 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 395 5 h37 kb_1459_395
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 400 2 h38 kb_1459_400
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 402 4 h39 kb_1459_402
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 406 4 h40 kb_1459_406
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 410 2 h41 kb_1459_410
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 412 5 h42 kb_1459_412
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 417 1 h43 kb_1459_417
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 418 6 h44 kb_1459_418
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 424 1 h45 kb_1459_424
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 425 2 h46 kb_1459_425
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 427 25 h47 kb_1459_427
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 459 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 452 7 h48 kb_1459_452
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 459 6 h49 kb_1459_459
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 465 2 h50 kb_1459_465
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 467 22 h51 kb_1459_467
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 489 72 h52 kb_1459_489
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 561 3 h53 kb_1459_561
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 564 2 h54 kb_1459_564
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 574 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 566 8 h55 kb_1459_566
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 574 9 h56 kb_1459_574
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 583 3 h57 kb_1459_583
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 586 3 h58 kb_1459_586
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 594 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 589 5 h59 kb_1459_589
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 599 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 594 5 h60 kb_1459_594
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 599 9 h61 kb_1459_599
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 608 32 h62 kb_1459_608
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 640 2 h63 kb_1459_640
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 642 6 h64 kb_1459_642
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 648 2 h65 kb_1459_648
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 650 22 h66 kb_1459_650
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 672 61 h67 kb_1459_672
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 743 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 733 10 h68 kb_1459_733
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 744 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 743 1 h69 kb_1459_743
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 748 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 744 4 h70 kb_1459_744
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 753 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 748 5 h71 kb_1459_748
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 753 8 h72 kb_1459_753
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 761 2 h73 kb_1459_761
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 763 4 h74 kb_1459_763
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 767 4 h75 kb_1459_767
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 771 4 h76 kb_1459_771
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 777 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 775 2 h77 kb_1459_775
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 777 6 h78 kb_1459_777
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 783 3 h79 kb_1459_783
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 790 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 786 4 h80 kb_1459_786
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 790 1 h81 kb_1459_790
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 793 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 791 2 h82 kb_1459_791
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 793 11 h83 kb_1459_793
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 815 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 804 11 h84 kb_1459_804
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 815 9 h85 kb_1459_815
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 824 4 h86 kb_1459_824
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 837 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1459.lits.getD i 0)) 0 828 9 h87 kb_1459_828
    exact h88
  have hg : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 837 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 4 = true := kg_1459_0
    have h1 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 5 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 4 1 h0 kg_1459_4
    have h2 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 18 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 5 13 h1 kg_1459_5
    have h3 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 19 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 18 1 h2 kg_1459_18
    have h4 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 28 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 19 9 h3 kg_1459_19
    have h5 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 29 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 28 1 h4 kg_1459_28
    have h6 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 30 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 29 1 h5 kg_1459_29
    have h7 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 48 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 30 18 h6 kg_1459_30
    have h8 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 155 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 48 107 h7 kg_1459_48
    have h9 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 167 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 155 12 h8 kg_1459_155
    have h10 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 171 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 167 4 h9 kg_1459_167
    have h11 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 199 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 171 28 h10 kg_1459_171
    have h12 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 205 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 199 6 h11 kg_1459_199
    have h13 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 207 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 205 2 h12 kg_1459_205
    have h14 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 228 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 207 21 h13 kg_1459_207
    have h15 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 238 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 228 10 h14 kg_1459_228
    have h16 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 272 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 238 34 h15 kg_1459_238
    have h17 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 308 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 272 36 h16 kg_1459_272
    have h18 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 310 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 308 2 h17 kg_1459_308
    have h19 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 311 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 310 1 h18 kg_1459_310
    have h20 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 318 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 311 7 h19 kg_1459_311
    have h21 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 324 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 318 6 h20 kg_1459_318
    have h22 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 344 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 324 20 h21 kg_1459_324
    have h23 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 346 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 344 2 h22 kg_1459_344
    have h24 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 356 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 346 10 h23 kg_1459_346
    have h25 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 357 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 356 1 h24 kg_1459_356
    have h26 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 358 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 357 1 h25 kg_1459_357
    have h27 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 360 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 358 2 h26 kg_1459_358
    have h28 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 363 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 360 3 h27 kg_1459_360
    have h29 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 365 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 363 2 h28 kg_1459_363
    have h30 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 367 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 365 2 h29 kg_1459_365
    have h31 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 375 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 367 8 h30 kg_1459_367
    have h32 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 378 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 375 3 h31 kg_1459_375
    have h33 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 380 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 378 2 h32 kg_1459_378
    have h34 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 387 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 380 7 h33 kg_1459_380
    have h35 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 390 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 387 3 h34 kg_1459_387
    have h36 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 394 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 390 4 h35 kg_1459_390
    have h37 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 395 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 394 1 h36 kg_1459_394
    have h38 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 400 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 395 5 h37 kg_1459_395
    have h39 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 402 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 400 2 h38 kg_1459_400
    have h40 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 406 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 402 4 h39 kg_1459_402
    have h41 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 410 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 406 4 h40 kg_1459_406
    have h42 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 412 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 410 2 h41 kg_1459_410
    have h43 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 417 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 412 5 h42 kg_1459_412
    have h44 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 418 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 417 1 h43 kg_1459_417
    have h45 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 424 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 418 6 h44 kg_1459_418
    have h46 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 425 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 424 1 h45 kg_1459_424
    have h47 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 427 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 425 2 h46 kg_1459_425
    have h48 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 452 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 427 25 h47 kg_1459_427
    have h49 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 459 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 452 7 h48 kg_1459_452
    have h50 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 465 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 459 6 h49 kg_1459_459
    have h51 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 467 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 465 2 h50 kg_1459_465
    have h52 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 489 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 467 22 h51 kg_1459_467
    have h53 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 561 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 489 72 h52 kg_1459_489
    have h54 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 564 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 561 3 h53 kg_1459_561
    have h55 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 566 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 564 2 h54 kg_1459_564
    have h56 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 574 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 566 8 h55 kg_1459_566
    have h57 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 583 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 574 9 h56 kg_1459_574
    have h58 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 586 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 583 3 h57 kg_1459_583
    have h59 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 589 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 586 3 h58 kg_1459_586
    have h60 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 594 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 589 5 h59 kg_1459_589
    have h61 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 599 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 594 5 h60 kg_1459_594
    have h62 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 608 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 599 9 h61 kg_1459_599
    have h63 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 640 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 608 32 h62 kg_1459_608
    have h64 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 642 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 640 2 h63 kg_1459_640
    have h65 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 648 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 642 6 h64 kg_1459_642
    have h66 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 650 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 648 2 h65 kg_1459_648
    have h67 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 672 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 650 22 h66 kg_1459_650
    have h68 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 733 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 672 61 h67 kg_1459_672
    have h69 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 743 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 733 10 h68 kg_1459_733
    have h70 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 744 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 743 1 h69 kg_1459_743
    have h71 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 748 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 744 4 h70 kg_1459_744
    have h72 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 753 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 748 5 h71 kg_1459_748
    have h73 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 761 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 753 8 h72 kg_1459_753
    have h74 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 763 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 761 2 h73 kg_1459_761
    have h75 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 767 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 763 4 h74 kg_1459_763
    have h76 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 771 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 767 4 h75 kg_1459_767
    have h77 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 775 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 771 4 h76 kg_1459_771
    have h78 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 777 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 775 2 h77 kg_1459_775
    have h79 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 783 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 777 6 h78 kg_1459_777
    have h80 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 786 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 783 3 h79 kg_1459_783
    have h81 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 790 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 786 4 h80 kg_1459_786
    have h82 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 791 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 790 1 h81 kg_1459_790
    have h83 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 793 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 791 2 h82 kg_1459_791
    have h84 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 804 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 793 11 h83 kg_1459_793
    have h85 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 815 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 804 11 h84 kg_1459_804
    have h86 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 824 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 815 9 h85 kg_1459_815
    have h87 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 828 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 824 4 h86 kg_1459_824
    have h88 : IPChk.allR (Pts.glueIB K1459.lits KW_1459) 0 837 = true := IPChk.allR_join (Pts.glueIB K1459.lits KW_1459) 0 828 9 h87 kg_1459_828
    exact h88
  have hlen : K1459.lits.length = 837 := by decide
  intro k h1 h2
  obtain rfl : k = 1459 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1459) K1459.lits KW_1459
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_298 : ∀ k, 1460 ≤ k → k < 1462 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1460 JW_1460 1460 2 jr_1460
theorem jr6_299 : ∀ k, 1462 ≤ k → k < 1463 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 627 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 7 = true := kb_1462_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 7 10 h0 kb_1462_7
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 17 8 h1 kb_1462_17
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 25 13 h2 kb_1462_25
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 38 6 h3 kb_1462_38
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 44 2 h4 kb_1462_44
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 46 22 h5 kb_1462_46
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 68 6 h6 kb_1462_68
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 74 2 h7 kb_1462_74
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 76 16 h8 kb_1462_76
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 92 17 h9 kb_1462_92
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 109 4 h10 kb_1462_109
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 113 21 h11 kb_1462_113
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 134 6 h12 kb_1462_134
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 140 14 h13 kb_1462_140
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 154 2 h14 kb_1462_154
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 156 6 h15 kb_1462_156
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 162 2 h16 kb_1462_162
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 164 21 h17 kb_1462_164
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 185 2 h18 kb_1462_185
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 187 4 h19 kb_1462_187
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 191 8 h20 kb_1462_191
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 199 21 h21 kb_1462_199
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 220 32 h22 kb_1462_220
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 252 24 h23 kb_1462_252
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 276 26 h24 kb_1462_276
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 304 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 302 2 h25 kb_1462_302
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 304 6 h26 kb_1462_304
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 310 8 h27 kb_1462_310
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 318 15 h28 kb_1462_318
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 333 2 h29 kb_1462_333
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 335 22 h30 kb_1462_335
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 357 24 h31 kb_1462_357
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 381 14 h32 kb_1462_381
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 395 8 h33 kb_1462_395
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 403 15 h34 kb_1462_403
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 418 5 h35 kb_1462_418
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 423 2 h36 kb_1462_423
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 425 13 h37 kb_1462_425
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 458 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 438 20 h38 kb_1462_438
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 458 9 h39 kb_1462_458
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 470 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 467 3 h40 kb_1462_467
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 470 12 h41 kb_1462_470
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 482 34 h42 kb_1462_482
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 516 14 h43 kb_1462_516
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 543 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 530 13 h44 kb_1462_530
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 543 32 h45 kb_1462_543
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 575 35 h46 kb_1462_575
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 627 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 0 610 17 h47 kb_1462_610
    exact h48
  have hg : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 627 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 7 = true := kg_1462_0
    have h1 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 17 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 7 10 h0 kg_1462_7
    have h2 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 25 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 17 8 h1 kg_1462_17
    have h3 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 38 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 25 13 h2 kg_1462_25
    have h4 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 44 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 38 6 h3 kg_1462_38
    have h5 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 46 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 44 2 h4 kg_1462_44
    have h6 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 68 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 46 22 h5 kg_1462_46
    have h7 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 74 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 68 6 h6 kg_1462_68
    have h8 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 76 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 74 2 h7 kg_1462_74
    have h9 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 92 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 76 16 h8 kg_1462_76
    have h10 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 109 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 92 17 h9 kg_1462_92
    have h11 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 113 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 109 4 h10 kg_1462_109
    have h12 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 134 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 113 21 h11 kg_1462_113
    have h13 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 140 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 134 6 h12 kg_1462_134
    have h14 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 154 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 140 14 h13 kg_1462_140
    have h15 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 156 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 154 2 h14 kg_1462_154
    have h16 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 162 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 156 6 h15 kg_1462_156
    have h17 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 164 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 162 2 h16 kg_1462_162
    have h18 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 185 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 164 21 h17 kg_1462_164
    have h19 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 187 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 185 2 h18 kg_1462_185
    have h20 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 191 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 187 4 h19 kg_1462_187
    have h21 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 199 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 191 8 h20 kg_1462_191
    have h22 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 220 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 199 21 h21 kg_1462_199
    have h23 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 252 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 220 32 h22 kg_1462_220
    have h24 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 276 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 252 24 h23 kg_1462_252
    have h25 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 302 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 276 26 h24 kg_1462_276
    have h26 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 304 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 302 2 h25 kg_1462_302
    have h27 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 310 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 304 6 h26 kg_1462_304
    have h28 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 318 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 310 8 h27 kg_1462_310
    have h29 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 333 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 318 15 h28 kg_1462_318
    have h30 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 335 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 333 2 h29 kg_1462_333
    have h31 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 357 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 335 22 h30 kg_1462_335
    have h32 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 381 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 357 24 h31 kg_1462_357
    have h33 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 395 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 381 14 h32 kg_1462_381
    have h34 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 403 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 395 8 h33 kg_1462_395
    have h35 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 418 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 403 15 h34 kg_1462_403
    have h36 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 423 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 418 5 h35 kg_1462_418
    have h37 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 425 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 423 2 h36 kg_1462_423
    have h38 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 438 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 425 13 h37 kg_1462_425
    have h39 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 458 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 438 20 h38 kg_1462_438
    have h40 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 467 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 458 9 h39 kg_1462_458
    have h41 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 470 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 467 3 h40 kg_1462_467
    have h42 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 482 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 470 12 h41 kg_1462_470
    have h43 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 516 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 482 34 h42 kg_1462_482
    have h44 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 530 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 516 14 h43 kg_1462_516
    have h45 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 543 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 530 13 h44 kg_1462_530
    have h46 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 575 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 543 32 h45 kg_1462_543
    have h47 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 610 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 575 35 h46 kg_1462_575
    have h48 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 0 627 = true := IPChk.allR_join (Pts.glueIB K1462.lits KW_1462) 0 610 17 h47 kg_1462_610
    exact h48
  have hlen : K1462.lits.length = 627 := by decide
  intro k h1 h2
  obtain rfl : k = 1462 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1462) K1462.lits KW_1462
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)

theorem grp6_11 : ∀ k, 1406 ≤ k → k < 1463 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_287
  have a1 := Pts.fa_join a0 jr6_288
  have a2 := Pts.fa_join a1 jr6_289
  have a3 := Pts.fa_join a2 jr6_290
  have a4 := Pts.fa_join a3 jr6_291
  have a5 := Pts.fa_join a4 jr6_292
  have a6 := Pts.fa_join a5 jr6_293
  have a7 := Pts.fa_join a6 jr6_294
  have a8 := Pts.fa_join a7 jr6_295
  have a9 := Pts.fa_join a8 jr6_296
  have a10 := Pts.fa_join a9 jr6_297
  have a11 := Pts.fa_join a10 jr6_298
  have a12 := Pts.fa_join a11 jr6_299
  exact a12

end B334.E1x.Pts.S707
