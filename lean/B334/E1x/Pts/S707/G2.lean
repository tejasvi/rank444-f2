import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J289
import B334.E1x.Pts.S707.J294
import B334.E1x.Pts.S707.K287L
import B334.E1x.Pts.S707.K288L
import B334.E1x.Pts.S707.K293L
import B334.E1x.Pts.S707.K287Q0
import B334.E1x.Pts.S707.K287Q1
import B334.E1x.Pts.S707.K287Q2
import B334.E1x.Pts.S707.K287Q3
import B334.E1x.Pts.S707.K287Q4
import B334.E1x.Pts.S707.K287Q5
import B334.E1x.Pts.S707.K287Q6
import B334.E1x.Pts.S707.K287Q7
import B334.E1x.Pts.S707.K287Q8
import B334.E1x.Pts.S707.K287Q9
import B334.E1x.Pts.S707.K288C0
import B334.E1x.Pts.S707.K293Q0
import B334.E1x.Pts.S707.K293Q1
import B334.E1x.Pts.S707.K293Q2
import B334.E1x.Pts.S707.K293Q3
import B334.E1x.Pts.S707.K293Q4
import B334.E1x.Pts.S707.K293Q5
import B334.E1x.Pts.S707.K293Q6
import B334.E1x.Pts.S707.K293Q7
import B334.E1x.Pts.S707.K293Q8
import B334.E1x.Pts.S707.K293Q9
import B334.E1x.Pts.S707.K287Q10
import B334.E1x.Pts.S707.K287Q11
import B334.E1x.Pts.S707.K287Q12
import B334.E1x.Pts.S707.K287Q13
import B334.E1x.Pts.S707.K287Q14
import B334.E1x.Pts.S707.K287Q15
import B334.E1x.Pts.S707.K287Q16
import B334.E1x.Pts.S707.K287Q17
import B334.E1x.Pts.S707.K287Q18
import B334.E1x.Pts.S707.K287Q19
import B334.E1x.Pts.S707.K287Q20
import B334.E1x.Pts.S707.K287Q21
import B334.E1x.Pts.S707.K287Q22
import B334.E1x.Pts.S707.K287Q23
import B334.E1x.Pts.S707.K287Q24
import B334.E1x.Pts.S707.K287Q25
import B334.E1x.Pts.S707.K287Q26
import B334.E1x.Pts.S707.K287Q27
import B334.E1x.Pts.S707.K287Q28
import B334.E1x.Pts.S707.K287Q29
import B334.E1x.Pts.S707.K287Q30
import B334.E1x.Pts.S707.K287Q31
import B334.E1x.Pts.S707.K287Q32
import B334.E1x.Pts.S707.K287Q33
import B334.E1x.Pts.S707.K287Q34
import B334.E1x.Pts.S707.K287Q35
import B334.E1x.Pts.S707.K293Q10
import B334.E1x.Pts.S707.K293Q11
import B334.E1x.Pts.S707.K293Q12
import B334.E1x.Pts.S707.K293Q13
import B334.E1x.Pts.S707.K293Q14
import B334.E1x.Pts.S707.K293Q15
import B334.E1x.Pts.S707.K293Q16
import B334.E1x.Pts.S707.K293Q17
import B334.E1x.Pts.S707.K293Q18
import B334.E1x.Pts.S707.K293Q19
import B334.E1x.Pts.S707.K293Q20
import B334.E1x.Pts.S707.K293Q21
import B334.E1x.Pts.S707.K293Q22

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 287 … 297 (stage707_v6): the v5 Fin's job blocks r64 … r70 as
theorems, joined into `grp6_2` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_64 : ∀ k, 287 ≤ k → k < 288 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5151 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1 = true := kb_287_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1 1 h0 kb_287_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2 2 h1 kb_287_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4 4 h2 kb_287_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 8 25 h3 kb_287_8
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 33 7 h4 kb_287_33
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 40 18 h5 kb_287_40
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 58 4 h6 kb_287_58
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 62 2 h7 kb_287_62
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 64 8 h8 kb_287_64
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 72 11 h9 kb_287_72
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 83 6 h10 kb_287_83
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 89 2 h11 kb_287_89
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 91 8 h12 kb_287_91
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 99 10 h13 kb_287_99
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 109 16 h14 kb_287_109
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 125 8 h15 kb_287_125
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 133 9 h16 kb_287_133
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 142 3 h17 kb_287_142
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 145 18 h18 kb_287_145
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 163 24 h19 kb_287_163
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 187 10 h20 kb_287_187
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 197 14 h21 kb_287_197
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 211 16 h22 kb_287_211
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 227 2 h23 kb_287_227
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 229 1 h24 kb_287_229
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 230 13 h25 kb_287_230
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 243 16 h26 kb_287_243
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 259 1 h27 kb_287_259
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 260 13 h28 kb_287_260
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 273 2 h29 kb_287_273
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 304 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 275 29 h30 kb_287_275
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 304 2 h31 kb_287_304
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 306 6 h32 kb_287_306
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 314 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 312 2 h33 kb_287_312
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 314 21 h34 kb_287_314
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 335 6 h35 kb_287_335
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 341 2 h36 kb_287_341
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 343 19 h37 kb_287_343
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 362 4 h38 kb_287_362
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 366 15 h39 kb_287_366
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 381 11 h40 kb_287_381
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 392 3 h41 kb_287_392
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 395 10 h42 kb_287_395
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 405 2 h43 kb_287_405
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 407 29 h44 kb_287_407
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 436 2 h45 kb_287_436
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 438 6 h46 kb_287_438
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 444 2 h47 kb_287_444
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 446 17 h48 kb_287_446
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 463 6 h49 kb_287_463
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 469 3 h50 kb_287_469
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 472 20 h51 kb_287_472
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 492 14 h52 kb_287_492
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 506 5 h53 kb_287_506
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 511 7 h54 kb_287_511
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 518 2 h55 kb_287_518
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 520 29 h56 kb_287_520
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 549 2 h57 kb_287_549
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 551 6 h58 kb_287_551
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 557 2 h59 kb_287_557
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 559 17 h60 kb_287_559
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 576 6 h61 kb_287_576
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 582 2 h62 kb_287_582
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 584 16 h63 kb_287_584
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 600 1 h64 kb_287_600
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 601 19 h65 kb_287_601
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 620 30 h66 kb_287_620
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 650 2 h67 kb_287_650
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 667 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 652 15 h68 kb_287_652
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 669 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 667 2 h69 kb_287_667
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 669 15 h70 kb_287_669
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 684 2 h71 kb_287_684
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 713 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 686 27 h72 kb_287_686
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 713 7 h73 kb_287_713
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 720 2 h74 kb_287_720
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 722 1 h75 kb_287_722
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 723 10 h76 kb_287_723
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 733 1 h77 kb_287_733
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 734 1 h78 kb_287_734
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 744 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 735 9 h79 kb_287_735
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 780 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 744 36 h80 kb_287_744
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 780 7 h81 kb_287_780
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 788 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 787 1 h82 kb_287_787
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 788 9 h83 kb_287_788
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 797 1 h84 kb_287_797
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 798 24 h85 kb_287_798
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 822 7 h86 kb_287_822
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 835 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 829 6 h87 kb_287_829
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 837 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 835 2 h88 kb_287_835
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 859 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 837 22 h89 kb_287_837
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 859 3 h90 kb_287_859
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 923 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 862 61 h91 kb_287_862
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 929 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 923 6 h92 kb_287_923
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 931 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 929 2 h93 kb_287_929
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 942 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 931 11 h94 kb_287_931
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 942 1 h95 kb_287_942
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 944 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 943 1 h96 kb_287_943
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 951 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 944 7 h97 kb_287_944
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 952 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 951 1 h98 kb_287_951
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 971 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 952 19 h99 kb_287_952
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 983 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 971 12 h100 kb_287_971
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 983 6 h101 kb_287_983
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 989 2 h102 kb_287_989
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 991 22 h103 kb_287_991
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1016 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1013 3 h104 kb_287_1013
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1086 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1016 70 h105 kb_287_1016
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1090 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1086 4 h106 kb_287_1086
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1090 11 h107 kb_287_1090
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1101 8 h108 kb_287_1101
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1109 26 h109 kb_287_1109
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1135 22 h110 kb_287_1135
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1157 20 h111 kb_287_1157
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1177 2 h112 kb_287_1177
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1179 23 h113 kb_287_1179
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1202 2 h114 kb_287_1202
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1204 28 h115 kb_287_1204
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1232 38 h116 kb_287_1232
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1270 2 h117 kb_287_1270
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1272 6 h118 kb_287_1272
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1287 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1278 9 h119 kb_287_1278
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1287 34 h120 kb_287_1287
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1325 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1321 4 h121 kb_287_1321
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1325 1 h122 kb_287_1325
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1326 5 h123 kb_287_1326
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1331 21 h124 kb_287_1331
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1352 10 h125 kb_287_1352
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1362 6 h126 kb_287_1362
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1368 2 h127 kb_287_1368
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1370 22 h128 kb_287_1370
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1392 41 h129 kb_287_1392
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1441 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1433 8 h130 kb_287_1433
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1441 10 h131 kb_287_1441
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1451 2 h132 kb_287_1451
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1453 12 h133 kb_287_1453
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1465 39 h134 kb_287_1465
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1504 2 h135 kb_287_1504
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1506 13 h136 kb_287_1506
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1519 6 h137 kb_287_1519
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1525 2 h138 kb_287_1525
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1527 20 h139 kb_287_1527
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1547 3 h140 kb_287_1547
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1550 30 h141 kb_287_1550
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1580 40 h142 kb_287_1580
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1627 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1620 7 h143 kb_287_1620
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1627 2 h144 kb_287_1627
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1629 5 h145 kb_287_1629
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1634 1 h146 kb_287_1634
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1635 9 h147 kb_287_1635
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1679 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1644 35 h148 kb_287_1644
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1679 6 h149 kb_287_1679
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1685 1 h150 kb_287_1685
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1686 13 h151 kb_287_1686
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1700 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1699 1 h152 kb_287_1699
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1703 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1700 3 h153 kb_287_1700
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1704 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1703 1 h154 kb_287_1703
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1710 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1704 6 h155 kb_287_1704
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1712 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1710 2 h156 kb_287_1710
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1712 4 h157 kb_287_1712
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1716 1 h158 kb_287_1716
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1717 6 h159 kb_287_1717
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1723 1 h160 kb_287_1723
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1724 8 h161 kb_287_1724
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1755 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1732 23 h162 kb_287_1732
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1776 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1755 21 h163 kb_287_1755
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1776 2 h164 kb_287_1776
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1778 13 h165 kb_287_1778
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1791 6 h166 kb_287_1791
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1797 1 h167 kb_287_1797
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1815 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1798 17 h168 kb_287_1798
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1815 5 h169 kb_287_1815
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1837 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1820 17 h170 kb_287_1820
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1879 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1837 42 h171 kb_287_1837
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1884 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1879 5 h172 kb_287_1879
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1906 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1884 22 h173 kb_287_1884
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1934 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1906 28 h174 kb_287_1906
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1934 29 h175 kb_287_1934
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2021 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 1963 58 h176 kb_287_1963
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2037 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2021 16 h177 kb_287_2021
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2039 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2037 2 h178 kb_287_2037
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2039 58 h179 kb_287_2039
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2097 60 h180 kb_287_2097
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2157 2 h181 kb_287_2157
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2159 21 h182 kb_287_2159
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2180 2 h183 kb_287_2180
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2182 50 h184 kb_287_2182
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2232 70 h185 kb_287_2232
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2302 1 h186 kb_287_2302
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2346 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2303 43 h187 kb_287_2303
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2346 1 h188 kb_287_2346
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2347 14 h189 kb_287_2347
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2361 47 h190 kb_287_2361
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2408 76 h191 kb_287_2408
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2484 1 h192 kb_287_2484
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2485 15 h193 kb_287_2485
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2500 15 h194 kb_287_2500
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2515 1 h195 kb_287_2515
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2516 9 h196 kb_287_2516
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2525 2 h197 kb_287_2525
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2527 6 h198 kb_287_2527
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2533 1 h199 kb_287_2533
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2534 16 h200 kb_287_2534
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2550 1 h201 kb_287_2550
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2551 22 h202 kb_287_2551
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2573 7 h203 kb_287_2573
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2580 5 h204 kb_287_2580
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2585 1 h205 kb_287_2585
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2586 2 h206 kb_287_2586
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2588 47 h207 kb_287_2588
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2635 82 h208 kb_287_2635
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2718 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2717 1 h209 kb_287_2717
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2718 4 h210 kb_287_2718
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2746 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2722 24 h211 kb_287_2722
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2747 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2746 1 h212 kb_287_2746
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2747 9 h213 kb_287_2747
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2756 5 h214 kb_287_2756
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2774 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2761 13 h215 kb_287_2761
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2774 7 h216 kb_287_2774
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2781 5 h217 kb_287_2781
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2799 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2786 13 h218 kb_287_2786
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2799 45 h219 kb_287_2799
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2850 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2844 6 h220 kb_287_2844
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2851 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2850 1 h221 kb_287_2850
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2871 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2851 20 h222 kb_287_2851
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2871 32 h223 kb_287_2871
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2903 24 h224 kb_287_2903
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2928 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2927 1 h225 kb_287_2927
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2928 26 h226 kb_287_2928
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2954 1 h227 kb_287_2954
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2955 10 h228 kb_287_2955
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2967 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2965 2 h229 kb_287_2965
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 2967 55 h230 kb_287_2967
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3085 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3022 63 h231 kb_287_3022
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3086 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3085 1 h232 kb_287_3085
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3090 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3086 4 h233 kb_287_3086
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3090 24 h234 kb_287_3090
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3114 1 h235 kb_287_3114
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3115 9 h236 kb_287_3115
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3124 1 h237 kb_287_3124
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3125 4 h238 kb_287_3125
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3129 1 h239 kb_287_3129
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3130 8 h240 kb_287_3130
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3138 4 h241 kb_287_3138
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3142 8 h242 kb_287_3142
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3150 14 h243 kb_287_3150
    have h245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3164 13 h244 kb_287_3164
    have h246 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3177 26 h245 kb_287_3177
    have h247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3203 18 h246 kb_287_3203
    have h248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3221 4 h247 kb_287_3221
    have h249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3225 32 h248 kb_287_3225
    have h250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3257 33 h249 kb_287_3257
    have h251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3290 31 h250 kb_287_3290
    have h252 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3321 14 h251 kb_287_3321
    have h253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3335 6 h252 kb_287_3335
    have h254 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3341 52 h253 kb_287_3341
    have h255 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3393 67 h254 kb_287_3393
    have h256 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3460 13 h255 kb_287_3460
    have h257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3473 29 h256 kb_287_3473
    have h258 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3502 1 h257 kb_287_3502
    have h259 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3513 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3503 10 h258 kb_287_3503
    have h260 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3513 3 h259 kb_287_3513
    have h261 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3516 3 h260 kb_287_3516
    have h262 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3545 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3519 26 h261 kb_287_3519
    have h263 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3545 1 h262 kb_287_3545
    have h264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3546 6 h263 kb_287_3546
    have h265 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3552 4 h264 kb_287_3552
    have h266 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3556 5 h265 kb_287_3556
    have h267 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3561 5 h266 kb_287_3561
    have h268 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3566 10 h267 kb_287_3566
    have h269 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3576 6 h268 kb_287_3576
    have h270 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3587 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3582 5 h269 kb_287_3582
    have h271 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3587 15 h270 kb_287_3587
    have h272 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3602 41 h271 kb_287_3602
    have h273 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3649 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3643 6 h272 kb_287_3643
    have h274 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3649 1 h273 kb_287_3649
    have h275 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3650 18 h274 kb_287_3650
    have h276 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3700 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3668 32 h275 kb_287_3668
    have h277 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3718 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3700 18 h276 kb_287_3700
    have h278 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3749 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3718 31 h277 kb_287_3718
    have h279 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3749 9 h278 kb_287_3749
    have h280 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3762 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3758 4 h279 kb_287_3758
    have h281 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3762 8 h280 kb_287_3762
    have h282 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3770 1 h281 kb_287_3770
    have h283 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3771 4 h282 kb_287_3771
    have h284 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3775 6 h283 kb_287_3775
    have h285 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3782 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3781 1 h284 kb_287_3781
    have h286 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3792 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3782 10 h285 kb_287_3782
    have h287 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3809 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3792 17 h286 kb_287_3792
    have h288 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3809 105 h287 kb_287_3809
    have h289 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3919 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3914 5 h288 kb_287_3914
    have h290 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3939 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3919 20 h289 kb_287_3919
    have h291 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3946 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3939 7 h290 kb_287_3939
    have h292 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3975 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3946 29 h291 kb_287_3946
    have h293 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4011 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 3975 36 h292 kb_287_3975
    have h294 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4011 61 h293 kb_287_4011
    have h295 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4091 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4072 19 h294 kb_287_4072
    have h296 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4095 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4091 4 h295 kb_287_4091
    have h297 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4098 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4095 3 h296 kb_287_4095
    have h298 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4098 9 h297 kb_287_4098
    have h299 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4107 29 h298 kb_287_4107
    have h300 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4136 1 h299 kb_287_4136
    have h301 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4137 56 h300 kb_287_4137
    have h302 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4193 98 h301 kb_287_4193
    have h303 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4291 5 h302 kb_287_4291
    have h304 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4296 5 h303 kb_287_4296
    have h305 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4301 4 h304 kb_287_4301
    have h306 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4305 4 h305 kb_287_4305
    have h307 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4309 29 h306 kb_287_4309
    have h308 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4338 1 h307 kb_287_4338
    have h309 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4339 1 h308 kb_287_4339
    have h310 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4349 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4340 9 h309 kb_287_4340
    have h311 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4349 24 h310 kb_287_4349
    have h312 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4373 1 h311 kb_287_4373
    have h313 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4390 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4374 16 h312 kb_287_4374
    have h314 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4390 98 h313 kb_287_4390
    have h315 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4488 15 h314 kb_287_4488
    have h316 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4503 13 h315 kb_287_4503
    have h317 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4516 3 h316 kb_287_4516
    have h318 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4519 3 h317 kb_287_4519
    have h319 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4522 8 h318 kb_287_4522
    have h320 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4536 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4530 6 h319 kb_287_4530
    have h321 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4536 8 h320 kb_287_4536
    have h322 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4544 10 h321 kb_287_4544
    have h323 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4554 7 h322 kb_287_4554
    have h324 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4569 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4561 8 h323 kb_287_4561
    have h325 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4569 28 h324 kb_287_4569
    have h326 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4597 4 h325 kb_287_4597
    have h327 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4601 1 h326 kb_287_4601
    have h328 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4602 10 h327 kb_287_4602
    have h329 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4612 1 h328 kb_287_4612
    have h330 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4627 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4613 14 h329 kb_287_4613
    have h331 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4627 28 h330 kb_287_4627
    have h332 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4655 20 h331 kb_287_4655
    have h333 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4675 1 h332 kb_287_4675
    have h334 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4676 10 h333 kb_287_4676
    have h335 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4686 1 h334 kb_287_4686
    have h336 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4700 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4687 13 h335 kb_287_4687
    have h337 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4700 6 h336 kb_287_4700
    have h338 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4709 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4706 3 h337 kb_287_4706
    have h339 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4709 7 h338 kb_287_4709
    have h340 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4716 4 h339 kb_287_4716
    have h341 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4720 6 h340 kb_287_4720
    have h342 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4726 6 h341 kb_287_4726
    have h343 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4732 3 h342 kb_287_4732
    have h344 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4735 6 h343 kb_287_4735
    have h345 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4743 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4741 2 h344 kb_287_4741
    have h346 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4749 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4743 6 h345 kb_287_4743
    have h347 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4749 18 h346 kb_287_4749
    have h348 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4767 16 h347 kb_287_4767
    have h349 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4783 4 h348 kb_287_4783
    have h350 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4788 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4787 1 h349 kb_287_4787
    have h351 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4788 46 h350 kb_287_4788
    have h352 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4834 98 h351 kb_287_4834
    have h353 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4980 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4932 48 h352 kb_287_4932
    have h354 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5088 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 4980 108 h353 kb_287_4980
    have h355 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5088 32 h354 kb_287_5088
    have h356 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5120 28 h355 kb_287_5120
    have h357 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K287.lits.getD i 0)) 0 5148 3 h356 kb_287_5148
    exact h357
  have hg : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 5151 = true := by
    have h0 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1 = true := kg_287_0
    have h1 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1 1 h0 kg_287_1
    have h2 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2 2 h1 kg_287_2
    have h3 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 8 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4 4 h2 kg_287_4
    have h4 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 33 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 8 25 h3 kg_287_8
    have h5 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 40 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 33 7 h4 kg_287_33
    have h6 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 58 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 40 18 h5 kg_287_40
    have h7 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 62 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 58 4 h6 kg_287_58
    have h8 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 64 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 62 2 h7 kg_287_62
    have h9 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 72 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 64 8 h8 kg_287_64
    have h10 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 83 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 72 11 h9 kg_287_72
    have h11 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 89 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 83 6 h10 kg_287_83
    have h12 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 91 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 89 2 h11 kg_287_89
    have h13 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 99 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 91 8 h12 kg_287_91
    have h14 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 109 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 99 10 h13 kg_287_99
    have h15 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 125 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 109 16 h14 kg_287_109
    have h16 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 133 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 125 8 h15 kg_287_125
    have h17 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 142 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 133 9 h16 kg_287_133
    have h18 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 145 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 142 3 h17 kg_287_142
    have h19 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 163 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 145 18 h18 kg_287_145
    have h20 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 187 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 163 24 h19 kg_287_163
    have h21 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 197 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 187 10 h20 kg_287_187
    have h22 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 211 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 197 14 h21 kg_287_197
    have h23 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 227 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 211 16 h22 kg_287_211
    have h24 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 229 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 227 2 h23 kg_287_227
    have h25 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 230 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 229 1 h24 kg_287_229
    have h26 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 243 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 230 13 h25 kg_287_230
    have h27 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 259 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 243 16 h26 kg_287_243
    have h28 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 260 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 259 1 h27 kg_287_259
    have h29 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 273 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 260 13 h28 kg_287_260
    have h30 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 275 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 273 2 h29 kg_287_273
    have h31 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 304 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 275 29 h30 kg_287_275
    have h32 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 306 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 304 2 h31 kg_287_304
    have h33 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 312 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 306 6 h32 kg_287_306
    have h34 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 314 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 312 2 h33 kg_287_312
    have h35 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 335 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 314 21 h34 kg_287_314
    have h36 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 341 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 335 6 h35 kg_287_335
    have h37 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 343 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 341 2 h36 kg_287_341
    have h38 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 362 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 343 19 h37 kg_287_343
    have h39 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 366 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 362 4 h38 kg_287_362
    have h40 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 381 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 366 15 h39 kg_287_366
    have h41 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 392 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 381 11 h40 kg_287_381
    have h42 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 395 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 392 3 h41 kg_287_392
    have h43 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 405 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 395 10 h42 kg_287_395
    have h44 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 407 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 405 2 h43 kg_287_405
    have h45 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 436 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 407 29 h44 kg_287_407
    have h46 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 438 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 436 2 h45 kg_287_436
    have h47 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 444 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 438 6 h46 kg_287_438
    have h48 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 446 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 444 2 h47 kg_287_444
    have h49 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 463 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 446 17 h48 kg_287_446
    have h50 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 469 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 463 6 h49 kg_287_463
    have h51 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 472 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 469 3 h50 kg_287_469
    have h52 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 492 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 472 20 h51 kg_287_472
    have h53 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 506 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 492 14 h52 kg_287_492
    have h54 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 511 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 506 5 h53 kg_287_506
    have h55 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 518 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 511 7 h54 kg_287_511
    have h56 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 520 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 518 2 h55 kg_287_518
    have h57 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 549 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 520 29 h56 kg_287_520
    have h58 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 551 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 549 2 h57 kg_287_549
    have h59 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 557 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 551 6 h58 kg_287_551
    have h60 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 559 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 557 2 h59 kg_287_557
    have h61 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 576 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 559 17 h60 kg_287_559
    have h62 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 582 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 576 6 h61 kg_287_576
    have h63 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 584 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 582 2 h62 kg_287_582
    have h64 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 600 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 584 16 h63 kg_287_584
    have h65 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 601 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 600 1 h64 kg_287_600
    have h66 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 620 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 601 19 h65 kg_287_601
    have h67 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 650 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 620 30 h66 kg_287_620
    have h68 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 652 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 650 2 h67 kg_287_650
    have h69 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 667 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 652 15 h68 kg_287_652
    have h70 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 669 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 667 2 h69 kg_287_667
    have h71 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 684 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 669 15 h70 kg_287_669
    have h72 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 686 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 684 2 h71 kg_287_684
    have h73 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 713 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 686 27 h72 kg_287_686
    have h74 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 720 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 713 7 h73 kg_287_713
    have h75 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 722 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 720 2 h74 kg_287_720
    have h76 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 723 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 722 1 h75 kg_287_722
    have h77 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 733 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 723 10 h76 kg_287_723
    have h78 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 734 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 733 1 h77 kg_287_733
    have h79 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 735 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 734 1 h78 kg_287_734
    have h80 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 744 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 735 9 h79 kg_287_735
    have h81 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 780 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 744 36 h80 kg_287_744
    have h82 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 787 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 780 7 h81 kg_287_780
    have h83 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 788 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 787 1 h82 kg_287_787
    have h84 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 797 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 788 9 h83 kg_287_788
    have h85 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 798 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 797 1 h84 kg_287_797
    have h86 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 822 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 798 24 h85 kg_287_798
    have h87 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 829 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 822 7 h86 kg_287_822
    have h88 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 835 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 829 6 h87 kg_287_829
    have h89 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 837 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 835 2 h88 kg_287_835
    have h90 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 859 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 837 22 h89 kg_287_837
    have h91 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 862 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 859 3 h90 kg_287_859
    have h92 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 923 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 862 61 h91 kg_287_862
    have h93 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 929 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 923 6 h92 kg_287_923
    have h94 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 931 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 929 2 h93 kg_287_929
    have h95 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 942 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 931 11 h94 kg_287_931
    have h96 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 943 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 942 1 h95 kg_287_942
    have h97 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 944 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 943 1 h96 kg_287_943
    have h98 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 951 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 944 7 h97 kg_287_944
    have h99 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 952 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 951 1 h98 kg_287_951
    have h100 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 971 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 952 19 h99 kg_287_952
    have h101 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 983 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 971 12 h100 kg_287_971
    have h102 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 989 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 983 6 h101 kg_287_983
    have h103 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 991 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 989 2 h102 kg_287_989
    have h104 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1013 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 991 22 h103 kg_287_991
    have h105 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1016 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1013 3 h104 kg_287_1013
    have h106 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1086 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1016 70 h105 kg_287_1016
    have h107 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1090 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1086 4 h106 kg_287_1086
    have h108 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1101 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1090 11 h107 kg_287_1090
    have h109 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1109 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1101 8 h108 kg_287_1101
    have h110 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1135 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1109 26 h109 kg_287_1109
    have h111 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1157 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1135 22 h110 kg_287_1135
    have h112 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1177 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1157 20 h111 kg_287_1157
    have h113 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1179 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1177 2 h112 kg_287_1177
    have h114 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1202 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1179 23 h113 kg_287_1179
    have h115 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1204 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1202 2 h114 kg_287_1202
    have h116 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1232 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1204 28 h115 kg_287_1204
    have h117 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1270 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1232 38 h116 kg_287_1232
    have h118 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1272 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1270 2 h117 kg_287_1270
    have h119 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1278 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1272 6 h118 kg_287_1272
    have h120 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1287 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1278 9 h119 kg_287_1278
    have h121 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1321 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1287 34 h120 kg_287_1287
    have h122 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1325 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1321 4 h121 kg_287_1321
    have h123 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1326 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1325 1 h122 kg_287_1325
    have h124 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1331 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1326 5 h123 kg_287_1326
    have h125 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1352 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1331 21 h124 kg_287_1331
    have h126 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1362 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1352 10 h125 kg_287_1352
    have h127 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1368 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1362 6 h126 kg_287_1362
    have h128 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1370 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1368 2 h127 kg_287_1368
    have h129 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1392 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1370 22 h128 kg_287_1370
    have h130 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1433 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1392 41 h129 kg_287_1392
    have h131 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1441 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1433 8 h130 kg_287_1433
    have h132 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1451 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1441 10 h131 kg_287_1441
    have h133 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1453 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1451 2 h132 kg_287_1451
    have h134 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1465 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1453 12 h133 kg_287_1453
    have h135 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1504 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1465 39 h134 kg_287_1465
    have h136 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1506 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1504 2 h135 kg_287_1504
    have h137 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1519 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1506 13 h136 kg_287_1506
    have h138 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1525 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1519 6 h137 kg_287_1519
    have h139 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1527 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1525 2 h138 kg_287_1525
    have h140 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1547 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1527 20 h139 kg_287_1527
    have h141 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1550 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1547 3 h140 kg_287_1547
    have h142 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1580 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1550 30 h141 kg_287_1550
    have h143 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1620 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1580 40 h142 kg_287_1580
    have h144 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1627 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1620 7 h143 kg_287_1620
    have h145 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1629 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1627 2 h144 kg_287_1627
    have h146 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1634 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1629 5 h145 kg_287_1629
    have h147 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1635 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1634 1 h146 kg_287_1634
    have h148 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1644 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1635 9 h147 kg_287_1635
    have h149 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1679 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1644 35 h148 kg_287_1644
    have h150 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1685 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1679 6 h149 kg_287_1679
    have h151 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1686 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1685 1 h150 kg_287_1685
    have h152 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1699 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1686 13 h151 kg_287_1686
    have h153 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1700 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1699 1 h152 kg_287_1699
    have h154 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1703 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1700 3 h153 kg_287_1700
    have h155 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1704 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1703 1 h154 kg_287_1703
    have h156 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1710 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1704 6 h155 kg_287_1704
    have h157 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1712 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1710 2 h156 kg_287_1710
    have h158 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1716 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1712 4 h157 kg_287_1712
    have h159 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1717 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1716 1 h158 kg_287_1716
    have h160 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1723 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1717 6 h159 kg_287_1717
    have h161 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1724 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1723 1 h160 kg_287_1723
    have h162 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1732 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1724 8 h161 kg_287_1724
    have h163 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1755 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1732 23 h162 kg_287_1732
    have h164 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1776 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1755 21 h163 kg_287_1755
    have h165 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1778 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1776 2 h164 kg_287_1776
    have h166 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1791 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1778 13 h165 kg_287_1778
    have h167 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1797 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1791 6 h166 kg_287_1791
    have h168 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1798 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1797 1 h167 kg_287_1797
    have h169 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1815 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1798 17 h168 kg_287_1798
    have h170 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1820 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1815 5 h169 kg_287_1815
    have h171 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1837 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1820 17 h170 kg_287_1820
    have h172 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1879 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1837 42 h171 kg_287_1837
    have h173 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1884 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1879 5 h172 kg_287_1879
    have h174 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1906 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1884 22 h173 kg_287_1884
    have h175 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1934 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1906 28 h174 kg_287_1906
    have h176 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 1963 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1934 29 h175 kg_287_1934
    have h177 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2021 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 1963 58 h176 kg_287_1963
    have h178 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2037 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2021 16 h177 kg_287_2021
    have h179 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2039 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2037 2 h178 kg_287_2037
    have h180 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2097 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2039 58 h179 kg_287_2039
    have h181 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2157 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2097 60 h180 kg_287_2097
    have h182 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2159 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2157 2 h181 kg_287_2157
    have h183 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2180 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2159 21 h182 kg_287_2159
    have h184 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2182 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2180 2 h183 kg_287_2180
    have h185 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2232 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2182 50 h184 kg_287_2182
    have h186 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2302 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2232 70 h185 kg_287_2232
    have h187 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2303 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2302 1 h186 kg_287_2302
    have h188 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2346 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2303 43 h187 kg_287_2303
    have h189 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2347 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2346 1 h188 kg_287_2346
    have h190 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2361 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2347 14 h189 kg_287_2347
    have h191 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2408 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2361 47 h190 kg_287_2361
    have h192 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2484 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2408 76 h191 kg_287_2408
    have h193 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2485 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2484 1 h192 kg_287_2484
    have h194 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2500 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2485 15 h193 kg_287_2485
    have h195 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2515 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2500 15 h194 kg_287_2500
    have h196 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2516 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2515 1 h195 kg_287_2515
    have h197 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2525 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2516 9 h196 kg_287_2516
    have h198 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2527 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2525 2 h197 kg_287_2525
    have h199 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2533 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2527 6 h198 kg_287_2527
    have h200 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2534 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2533 1 h199 kg_287_2533
    have h201 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2550 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2534 16 h200 kg_287_2534
    have h202 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2551 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2550 1 h201 kg_287_2550
    have h203 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2573 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2551 22 h202 kg_287_2551
    have h204 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2580 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2573 7 h203 kg_287_2573
    have h205 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2585 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2580 5 h204 kg_287_2580
    have h206 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2586 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2585 1 h205 kg_287_2585
    have h207 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2588 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2586 2 h206 kg_287_2586
    have h208 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2635 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2588 47 h207 kg_287_2588
    have h209 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2717 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2635 82 h208 kg_287_2635
    have h210 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2718 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2717 1 h209 kg_287_2717
    have h211 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2722 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2718 4 h210 kg_287_2718
    have h212 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2746 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2722 24 h211 kg_287_2722
    have h213 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2747 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2746 1 h212 kg_287_2746
    have h214 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2756 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2747 9 h213 kg_287_2747
    have h215 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2761 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2756 5 h214 kg_287_2756
    have h216 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2774 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2761 13 h215 kg_287_2761
    have h217 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2781 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2774 7 h216 kg_287_2774
    have h218 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2786 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2781 5 h217 kg_287_2781
    have h219 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2799 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2786 13 h218 kg_287_2786
    have h220 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2844 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2799 45 h219 kg_287_2799
    have h221 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2850 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2844 6 h220 kg_287_2844
    have h222 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2851 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2850 1 h221 kg_287_2850
    have h223 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2871 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2851 20 h222 kg_287_2851
    have h224 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2903 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2871 32 h223 kg_287_2871
    have h225 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2927 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2903 24 h224 kg_287_2903
    have h226 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2928 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2927 1 h225 kg_287_2927
    have h227 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2954 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2928 26 h226 kg_287_2928
    have h228 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2955 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2954 1 h227 kg_287_2954
    have h229 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2965 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2955 10 h228 kg_287_2955
    have h230 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 2967 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2965 2 h229 kg_287_2965
    have h231 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3022 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 2967 55 h230 kg_287_2967
    have h232 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3085 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3022 63 h231 kg_287_3022
    have h233 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3086 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3085 1 h232 kg_287_3085
    have h234 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3090 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3086 4 h233 kg_287_3086
    have h235 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3114 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3090 24 h234 kg_287_3090
    have h236 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3115 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3114 1 h235 kg_287_3114
    have h237 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3124 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3115 9 h236 kg_287_3115
    have h238 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3125 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3124 1 h237 kg_287_3124
    have h239 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3129 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3125 4 h238 kg_287_3125
    have h240 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3130 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3129 1 h239 kg_287_3129
    have h241 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3138 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3130 8 h240 kg_287_3130
    have h242 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3142 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3138 4 h241 kg_287_3138
    have h243 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3150 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3142 8 h242 kg_287_3142
    have h244 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3164 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3150 14 h243 kg_287_3150
    have h245 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3177 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3164 13 h244 kg_287_3164
    have h246 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3203 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3177 26 h245 kg_287_3177
    have h247 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3221 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3203 18 h246 kg_287_3203
    have h248 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3225 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3221 4 h247 kg_287_3221
    have h249 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3257 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3225 32 h248 kg_287_3225
    have h250 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3290 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3257 33 h249 kg_287_3257
    have h251 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3321 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3290 31 h250 kg_287_3290
    have h252 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3335 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3321 14 h251 kg_287_3321
    have h253 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3341 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3335 6 h252 kg_287_3335
    have h254 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3393 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3341 52 h253 kg_287_3341
    have h255 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3460 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3393 67 h254 kg_287_3393
    have h256 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3473 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3460 13 h255 kg_287_3460
    have h257 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3502 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3473 29 h256 kg_287_3473
    have h258 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3503 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3502 1 h257 kg_287_3502
    have h259 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3513 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3503 10 h258 kg_287_3503
    have h260 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3516 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3513 3 h259 kg_287_3513
    have h261 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3519 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3516 3 h260 kg_287_3516
    have h262 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3545 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3519 26 h261 kg_287_3519
    have h263 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3546 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3545 1 h262 kg_287_3545
    have h264 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3552 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3546 6 h263 kg_287_3546
    have h265 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3556 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3552 4 h264 kg_287_3552
    have h266 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3561 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3556 5 h265 kg_287_3556
    have h267 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3566 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3561 5 h266 kg_287_3561
    have h268 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3576 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3566 10 h267 kg_287_3566
    have h269 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3582 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3576 6 h268 kg_287_3576
    have h270 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3587 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3582 5 h269 kg_287_3582
    have h271 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3602 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3587 15 h270 kg_287_3587
    have h272 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3643 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3602 41 h271 kg_287_3602
    have h273 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3649 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3643 6 h272 kg_287_3643
    have h274 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3650 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3649 1 h273 kg_287_3649
    have h275 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3668 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3650 18 h274 kg_287_3650
    have h276 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3700 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3668 32 h275 kg_287_3668
    have h277 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3718 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3700 18 h276 kg_287_3700
    have h278 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3749 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3718 31 h277 kg_287_3718
    have h279 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3758 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3749 9 h278 kg_287_3749
    have h280 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3762 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3758 4 h279 kg_287_3758
    have h281 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3770 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3762 8 h280 kg_287_3762
    have h282 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3771 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3770 1 h281 kg_287_3770
    have h283 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3775 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3771 4 h282 kg_287_3771
    have h284 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3781 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3775 6 h283 kg_287_3775
    have h285 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3782 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3781 1 h284 kg_287_3781
    have h286 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3792 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3782 10 h285 kg_287_3782
    have h287 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3809 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3792 17 h286 kg_287_3792
    have h288 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3914 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3809 105 h287 kg_287_3809
    have h289 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3919 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3914 5 h288 kg_287_3914
    have h290 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3939 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3919 20 h289 kg_287_3919
    have h291 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3946 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3939 7 h290 kg_287_3939
    have h292 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 3975 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3946 29 h291 kg_287_3946
    have h293 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4011 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 3975 36 h292 kg_287_3975
    have h294 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4072 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4011 61 h293 kg_287_4011
    have h295 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4091 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4072 19 h294 kg_287_4072
    have h296 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4095 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4091 4 h295 kg_287_4091
    have h297 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4098 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4095 3 h296 kg_287_4095
    have h298 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4107 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4098 9 h297 kg_287_4098
    have h299 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4136 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4107 29 h298 kg_287_4107
    have h300 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4137 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4136 1 h299 kg_287_4136
    have h301 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4193 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4137 56 h300 kg_287_4137
    have h302 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4291 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4193 98 h301 kg_287_4193
    have h303 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4296 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4291 5 h302 kg_287_4291
    have h304 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4301 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4296 5 h303 kg_287_4296
    have h305 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4305 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4301 4 h304 kg_287_4301
    have h306 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4309 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4305 4 h305 kg_287_4305
    have h307 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4338 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4309 29 h306 kg_287_4309
    have h308 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4339 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4338 1 h307 kg_287_4338
    have h309 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4340 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4339 1 h308 kg_287_4339
    have h310 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4349 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4340 9 h309 kg_287_4340
    have h311 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4373 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4349 24 h310 kg_287_4349
    have h312 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4374 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4373 1 h311 kg_287_4373
    have h313 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4390 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4374 16 h312 kg_287_4374
    have h314 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4488 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4390 98 h313 kg_287_4390
    have h315 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4503 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4488 15 h314 kg_287_4488
    have h316 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4516 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4503 13 h315 kg_287_4503
    have h317 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4519 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4516 3 h316 kg_287_4516
    have h318 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4522 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4519 3 h317 kg_287_4519
    have h319 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4530 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4522 8 h318 kg_287_4522
    have h320 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4536 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4530 6 h319 kg_287_4530
    have h321 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4544 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4536 8 h320 kg_287_4536
    have h322 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4554 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4544 10 h321 kg_287_4544
    have h323 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4561 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4554 7 h322 kg_287_4554
    have h324 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4569 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4561 8 h323 kg_287_4561
    have h325 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4597 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4569 28 h324 kg_287_4569
    have h326 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4601 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4597 4 h325 kg_287_4597
    have h327 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4602 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4601 1 h326 kg_287_4601
    have h328 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4612 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4602 10 h327 kg_287_4602
    have h329 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4613 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4612 1 h328 kg_287_4612
    have h330 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4627 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4613 14 h329 kg_287_4613
    have h331 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4655 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4627 28 h330 kg_287_4627
    have h332 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4675 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4655 20 h331 kg_287_4655
    have h333 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4676 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4675 1 h332 kg_287_4675
    have h334 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4686 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4676 10 h333 kg_287_4676
    have h335 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4687 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4686 1 h334 kg_287_4686
    have h336 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4700 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4687 13 h335 kg_287_4687
    have h337 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4706 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4700 6 h336 kg_287_4700
    have h338 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4709 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4706 3 h337 kg_287_4706
    have h339 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4716 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4709 7 h338 kg_287_4709
    have h340 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4720 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4716 4 h339 kg_287_4716
    have h341 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4726 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4720 6 h340 kg_287_4720
    have h342 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4732 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4726 6 h341 kg_287_4726
    have h343 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4735 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4732 3 h342 kg_287_4732
    have h344 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4741 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4735 6 h343 kg_287_4735
    have h345 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4743 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4741 2 h344 kg_287_4741
    have h346 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4749 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4743 6 h345 kg_287_4743
    have h347 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4767 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4749 18 h346 kg_287_4749
    have h348 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4783 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4767 16 h347 kg_287_4767
    have h349 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4787 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4783 4 h348 kg_287_4783
    have h350 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4788 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4787 1 h349 kg_287_4787
    have h351 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4834 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4788 46 h350 kg_287_4788
    have h352 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4932 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4834 98 h351 kg_287_4834
    have h353 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 4980 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4932 48 h352 kg_287_4932
    have h354 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 5088 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 4980 108 h353 kg_287_4980
    have h355 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 5120 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 5088 32 h354 kg_287_5088
    have h356 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 5148 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 5120 28 h355 kg_287_5120
    have h357 : IPChk.allR (Pts.glueIB K287.lits KW_287) 0 5151 = true := IPChk.allR_join (Pts.glueIB K287.lits KW_287) 0 5148 3 h356 kg_287_5148
    exact h357
  have hlen : K287.lits.length = 5151 := by decide
  intro k h1 h2
  obtain rfl : k = 287 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 287) K287.lits KW_287
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_65 : ∀ k, 288 ≤ k → k < 289 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 6 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 2 = true := kb_288_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 2 2 h0 kb_288_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K288.lits.getD i 0)) 0 4 2 h1 kb_288_4
    exact h2
  have hg : IPChk.allR (Pts.glueIB K288.lits KW_288) 0 6 = true := by
    have h0 : IPChk.allR (Pts.glueIB K288.lits KW_288) 0 2 = true := kg_288_0
    have h1 : IPChk.allR (Pts.glueIB K288.lits KW_288) 0 4 = true := IPChk.allR_join (Pts.glueIB K288.lits KW_288) 0 2 2 h0 kg_288_2
    have h2 : IPChk.allR (Pts.glueIB K288.lits KW_288) 0 6 = true := IPChk.allR_join (Pts.glueIB K288.lits KW_288) 0 4 2 h1 kg_288_4
    exact h2
  have hlen : K288.lits.length = 6 := by decide
  intro k h1 h2
  obtain rfl : k = 288 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 288) K288.lits KW_288
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_66 : ∀ k, 289 ≤ k → k < 291 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_289 JW_289 289 2 jr_289
theorem jr6_67 : ∀ k, 291 ≤ k → k < 292 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_289 JW_289 291 1 jr_291
theorem jr6_68 : ∀ k, 292 ≤ k → k < 293 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_289 JW_289 292 1 jr_292
theorem jr6_69 : ∀ k, 293 ≤ k → k < 294 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3176 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3 = true := kb_293_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3 4 h0 kb_293_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 7 8 h1 kb_293_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 15 2 h2 kb_293_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 17 7 h3 kb_293_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 24 2 h4 kb_293_24
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 26 9 h5 kb_293_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 35 7 h6 kb_293_35
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 42 8 h7 kb_293_42
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 50 12 h8 kb_293_50
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 62 9 h9 kb_293_62
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 71 1 h10 kb_293_71
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 72 1 h11 kb_293_72
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 73 12 h12 kb_293_73
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 85 19 h13 kb_293_85
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 104 7 h14 kb_293_104
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 111 22 h15 kb_293_111
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 133 1 h16 kb_293_133
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 134 1 h17 kb_293_134
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 135 1 h18 kb_293_135
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 136 20 h19 kb_293_136
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 156 3 h20 kb_293_156
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 159 7 h21 kb_293_159
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 166 26 h22 kb_293_166
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 192 1 h23 kb_293_192
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 193 19 h24 kb_293_193
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 212 44 h25 kb_293_212
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 295 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 256 39 h26 kb_293_256
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 295 8 h27 kb_293_295
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 303 9 h28 kb_293_303
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 312 9 h29 kb_293_312
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 321 2 h30 kb_293_321
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 323 29 h31 kb_293_323
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 352 2 h32 kb_293_352
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 354 6 h33 kb_293_354
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 360 2 h34 kb_293_360
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 362 20 h35 kb_293_362
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 391 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 382 9 h36 kb_293_382
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 391 2 h37 kb_293_391
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 393 14 h38 kb_293_393
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 407 9 h39 kb_293_407
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 416 2 h40 kb_293_416
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 418 3 h41 kb_293_418
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 421 2 h42 kb_293_421
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 423 29 h43 kb_293_423
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 461 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 452 9 h44 kb_293_452
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 461 22 h45 kb_293_461
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 483 11 h46 kb_293_483
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 494 5 h47 kb_293_494
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 499 26 h48 kb_293_499
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 525 2 h49 kb_293_525
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 527 24 h50 kb_293_527
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 551 6 h51 kb_293_551
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 571 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 557 14 h52 kb_293_557
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 571 1 h53 kb_293_571
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 572 1 h54 kb_293_572
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 574 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 573 1 h55 kb_293_573
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 574 1 h56 kb_293_574
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 575 3 h57 kb_293_575
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 578 1 h58 kb_293_578
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 579 1 h59 kb_293_579
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 580 2 h60 kb_293_580
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 582 3 h61 kb_293_582
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 585 1 h62 kb_293_585
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 586 2 h63 kb_293_586
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 588 15 h64 kb_293_588
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 603 6 h65 kb_293_603
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 609 2 h66 kb_293_609
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 611 41 h67 kb_293_611
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 652 72 h68 kb_293_652
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 724 2 h69 kb_293_724
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 726 14 h70 kb_293_726
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 740 2 h71 kb_293_740
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 747 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 742 5 h72 kb_293_742
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 747 14 h73 kb_293_747
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 761 17 h74 kb_293_761
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 778 6 h75 kb_293_778
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 784 5 h76 kb_293_784
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 789 19 h77 kb_293_789
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 808 20 h78 kb_293_808
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 828 13 h79 kb_293_828
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 841 1 h80 kb_293_841
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 842 20 h81 kb_293_842
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 879 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 862 17 h82 kb_293_862
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 879 20 h83 kb_293_879
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 909 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 899 10 h84 kb_293_899
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 913 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 909 4 h85 kb_293_909
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 940 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 913 27 h86 kb_293_913
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 940 23 h87 kb_293_940
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 979 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 963 16 h88 kb_293_963
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 985 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 979 6 h89 kb_293_979
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 987 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 985 2 h90 kb_293_985
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1008 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 987 21 h91 kb_293_987
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1010 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1008 2 h92 kb_293_1008
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1017 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1010 7 h93 kb_293_1010
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1019 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1017 2 h94 kb_293_1017
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1039 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1019 20 h95 kb_293_1019
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1041 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1039 2 h96 kb_293_1039
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1062 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1041 21 h97 kb_293_1041
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1070 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1062 8 h98 kb_293_1062
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1086 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1070 16 h99 kb_293_1070
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1089 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1086 3 h100 kb_293_1086
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1089 22 h101 kb_293_1089
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1111 5 h102 kb_293_1111
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1116 12 h103 kb_293_1116
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1128 16 h104 kb_293_1128
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1144 41 h105 kb_293_1144
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1185 2 h106 kb_293_1185
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1187 14 h107 kb_293_1187
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1201 23 h108 kb_293_1201
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1224 2 h109 kb_293_1224
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1226 6 h110 kb_293_1226
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1232 21 h111 kb_293_1232
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1253 6 h112 kb_293_1253
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1259 22 h113 kb_293_1259
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1281 37 h114 kb_293_1281
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1318 37 h115 kb_293_1318
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1355 13 h116 kb_293_1355
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1368 11 h117 kb_293_1368
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1379 2 h118 kb_293_1379
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1381 7 h119 kb_293_1381
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1388 20 h120 kb_293_1388
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1408 1 h121 kb_293_1408
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1409 2 h122 kb_293_1409
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1411 2 h123 kb_293_1411
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1413 2 h124 kb_293_1413
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1415 2 h125 kb_293_1415
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1417 3 h126 kb_293_1417
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1420 1 h127 kb_293_1420
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1421 9 h128 kb_293_1421
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1430 30 h129 kb_293_1430
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1460 59 h130 kb_293_1460
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1519 19 h131 kb_293_1519
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1571 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1538 33 h132 kb_293_1538
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1571 15 h133 kb_293_1571
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1593 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1586 7 h134 kb_293_1586
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1593 31 h135 kb_293_1593
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1624 73 h136 kb_293_1624
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1697 2 h137 kb_293_1697
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1699 25 h138 kb_293_1699
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1724 37 h139 kb_293_1724
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1761 2 h140 kb_293_1761
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1763 15 h141 kb_293_1763
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1778 6 h142 kb_293_1778
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1784 2 h143 kb_293_1784
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1809 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1786 23 h144 kb_293_1786
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1809 2 h145 kb_293_1809
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1831 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1811 20 h146 kb_293_1811
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1831 31 h147 kb_293_1831
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1862 24 h148 kb_293_1862
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1895 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1886 9 h149 kb_293_1886
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1895 4 h150 kb_293_1895
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1928 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1899 29 h151 kb_293_1899
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1942 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1928 14 h152 kb_293_1928
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1957 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1942 15 h153 kb_293_1942
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1968 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1957 11 h154 kb_293_1957
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1968 6 h155 kb_293_1968
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1974 20 h156 kb_293_1974
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1998 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1994 4 h157 kb_293_1994
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2000 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 1998 2 h158 kb_293_1998
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2000 13 h159 kb_293_2000
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2041 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2013 28 h160 kb_293_2013
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2048 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2041 7 h161 kb_293_2041
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2048 20 h162 kb_293_2048
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2073 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2068 5 h163 kb_293_2068
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2096 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2073 23 h164 kb_293_2073
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2096 6 h165 kb_293_2096
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2102 2 h166 kb_293_2102
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2104 19 h167 kb_293_2104
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2123 29 h168 kb_293_2123
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2152 5 h169 kb_293_2152
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2157 3 h170 kb_293_2157
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2160 19 h171 kb_293_2160
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2179 2 h172 kb_293_2179
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2181 20 h173 kb_293_2181
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2201 26 h174 kb_293_2201
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2227 8 h175 kb_293_2227
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2235 57 h176 kb_293_2235
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2292 55 h177 kb_293_2292
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2347 15 h178 kb_293_2347
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2362 36 h179 kb_293_2362
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2398 15 h180 kb_293_2398
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2413 1 h181 kb_293_2413
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2414 1 h182 kb_293_2414
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2415 15 h183 kb_293_2415
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2430 8 h184 kb_293_2430
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2462 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2438 24 h185 kb_293_2438
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2462 1 h186 kb_293_2462
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2463 2 h187 kb_293_2463
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2465 4 h188 kb_293_2465
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2470 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2469 1 h189 kb_293_2469
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2470 9 h190 kb_293_2470
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2479 1 h191 kb_293_2479
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2480 5 h192 kb_293_2480
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2485 23 h193 kb_293_2485
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2508 8 h194 kb_293_2508
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2516 6 h195 kb_293_2516
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2522 61 h196 kb_293_2522
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2583 17 h197 kb_293_2583
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2600 1 h198 kb_293_2600
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2601 11 h199 kb_293_2601
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2612 6 h200 kb_293_2612
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2619 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2618 1 h201 kb_293_2618
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2645 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2619 26 h202 kb_293_2619
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2645 1 h203 kb_293_2645
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2646 7 h204 kb_293_2646
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2653 17 h205 kb_293_2653
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2670 15 h206 kb_293_2670
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2685 10 h207 kb_293_2685
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2695 2 h208 kb_293_2695
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2703 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2697 6 h209 kb_293_2697
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2703 17 h210 kb_293_2703
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2720 19 h211 kb_293_2720
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2739 28 h212 kb_293_2739
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2767 37 h213 kb_293_2767
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2863 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2804 59 h214 kb_293_2804
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2863 4 h215 kb_293_2863
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2867 57 h216 kb_293_2867
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2924 34 h217 kb_293_2924
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2987 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2958 29 h218 kb_293_2958
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2987 2 h219 kb_293_2987
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2995 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2989 6 h220 kb_293_2989
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 2995 10 h221 kb_293_2995
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3073 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3005 68 h222 kb_293_3005
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3085 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3073 12 h223 kb_293_3073
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3095 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3085 10 h224 kb_293_3085
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3095 16 h225 kb_293_3095
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3111 6 h226 kb_293_3111
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3117 31 h227 kb_293_3117
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3148 21 h228 kb_293_3148
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3169 3 h229 kb_293_3169
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 0 3172 4 h230 kb_293_3172
    exact h231
  have hg : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3176 = true := by
    have h0 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3 = true := kg_293_0
    have h1 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 7 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3 4 h0 kg_293_3
    have h2 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 15 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 7 8 h1 kg_293_7
    have h3 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 17 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 15 2 h2 kg_293_15
    have h4 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 24 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 17 7 h3 kg_293_17
    have h5 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 26 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 24 2 h4 kg_293_24
    have h6 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 35 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 26 9 h5 kg_293_26
    have h7 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 42 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 35 7 h6 kg_293_35
    have h8 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 50 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 42 8 h7 kg_293_42
    have h9 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 62 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 50 12 h8 kg_293_50
    have h10 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 71 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 62 9 h9 kg_293_62
    have h11 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 72 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 71 1 h10 kg_293_71
    have h12 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 73 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 72 1 h11 kg_293_72
    have h13 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 85 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 73 12 h12 kg_293_73
    have h14 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 104 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 85 19 h13 kg_293_85
    have h15 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 111 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 104 7 h14 kg_293_104
    have h16 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 133 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 111 22 h15 kg_293_111
    have h17 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 134 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 133 1 h16 kg_293_133
    have h18 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 135 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 134 1 h17 kg_293_134
    have h19 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 136 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 135 1 h18 kg_293_135
    have h20 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 156 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 136 20 h19 kg_293_136
    have h21 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 159 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 156 3 h20 kg_293_156
    have h22 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 166 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 159 7 h21 kg_293_159
    have h23 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 192 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 166 26 h22 kg_293_166
    have h24 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 193 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 192 1 h23 kg_293_192
    have h25 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 212 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 193 19 h24 kg_293_193
    have h26 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 256 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 212 44 h25 kg_293_212
    have h27 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 295 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 256 39 h26 kg_293_256
    have h28 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 303 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 295 8 h27 kg_293_295
    have h29 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 312 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 303 9 h28 kg_293_303
    have h30 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 321 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 312 9 h29 kg_293_312
    have h31 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 323 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 321 2 h30 kg_293_321
    have h32 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 352 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 323 29 h31 kg_293_323
    have h33 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 354 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 352 2 h32 kg_293_352
    have h34 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 360 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 354 6 h33 kg_293_354
    have h35 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 362 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 360 2 h34 kg_293_360
    have h36 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 382 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 362 20 h35 kg_293_362
    have h37 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 391 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 382 9 h36 kg_293_382
    have h38 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 393 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 391 2 h37 kg_293_391
    have h39 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 407 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 393 14 h38 kg_293_393
    have h40 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 416 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 407 9 h39 kg_293_407
    have h41 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 418 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 416 2 h40 kg_293_416
    have h42 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 421 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 418 3 h41 kg_293_418
    have h43 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 423 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 421 2 h42 kg_293_421
    have h44 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 452 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 423 29 h43 kg_293_423
    have h45 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 461 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 452 9 h44 kg_293_452
    have h46 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 483 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 461 22 h45 kg_293_461
    have h47 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 494 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 483 11 h46 kg_293_483
    have h48 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 499 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 494 5 h47 kg_293_494
    have h49 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 525 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 499 26 h48 kg_293_499
    have h50 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 527 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 525 2 h49 kg_293_525
    have h51 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 551 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 527 24 h50 kg_293_527
    have h52 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 557 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 551 6 h51 kg_293_551
    have h53 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 571 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 557 14 h52 kg_293_557
    have h54 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 572 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 571 1 h53 kg_293_571
    have h55 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 573 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 572 1 h54 kg_293_572
    have h56 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 574 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 573 1 h55 kg_293_573
    have h57 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 575 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 574 1 h56 kg_293_574
    have h58 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 578 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 575 3 h57 kg_293_575
    have h59 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 579 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 578 1 h58 kg_293_578
    have h60 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 580 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 579 1 h59 kg_293_579
    have h61 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 582 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 580 2 h60 kg_293_580
    have h62 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 585 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 582 3 h61 kg_293_582
    have h63 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 586 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 585 1 h62 kg_293_585
    have h64 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 588 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 586 2 h63 kg_293_586
    have h65 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 603 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 588 15 h64 kg_293_588
    have h66 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 609 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 603 6 h65 kg_293_603
    have h67 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 611 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 609 2 h66 kg_293_609
    have h68 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 652 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 611 41 h67 kg_293_611
    have h69 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 724 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 652 72 h68 kg_293_652
    have h70 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 726 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 724 2 h69 kg_293_724
    have h71 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 740 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 726 14 h70 kg_293_726
    have h72 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 742 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 740 2 h71 kg_293_740
    have h73 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 747 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 742 5 h72 kg_293_742
    have h74 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 761 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 747 14 h73 kg_293_747
    have h75 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 778 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 761 17 h74 kg_293_761
    have h76 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 784 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 778 6 h75 kg_293_778
    have h77 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 789 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 784 5 h76 kg_293_784
    have h78 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 808 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 789 19 h77 kg_293_789
    have h79 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 828 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 808 20 h78 kg_293_808
    have h80 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 841 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 828 13 h79 kg_293_828
    have h81 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 842 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 841 1 h80 kg_293_841
    have h82 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 862 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 842 20 h81 kg_293_842
    have h83 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 879 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 862 17 h82 kg_293_862
    have h84 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 899 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 879 20 h83 kg_293_879
    have h85 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 909 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 899 10 h84 kg_293_899
    have h86 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 913 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 909 4 h85 kg_293_909
    have h87 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 940 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 913 27 h86 kg_293_913
    have h88 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 963 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 940 23 h87 kg_293_940
    have h89 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 979 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 963 16 h88 kg_293_963
    have h90 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 985 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 979 6 h89 kg_293_979
    have h91 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 987 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 985 2 h90 kg_293_985
    have h92 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1008 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 987 21 h91 kg_293_987
    have h93 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1010 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1008 2 h92 kg_293_1008
    have h94 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1017 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1010 7 h93 kg_293_1010
    have h95 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1019 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1017 2 h94 kg_293_1017
    have h96 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1039 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1019 20 h95 kg_293_1019
    have h97 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1041 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1039 2 h96 kg_293_1039
    have h98 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1062 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1041 21 h97 kg_293_1041
    have h99 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1070 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1062 8 h98 kg_293_1062
    have h100 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1086 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1070 16 h99 kg_293_1070
    have h101 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1089 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1086 3 h100 kg_293_1086
    have h102 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1111 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1089 22 h101 kg_293_1089
    have h103 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1116 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1111 5 h102 kg_293_1111
    have h104 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1128 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1116 12 h103 kg_293_1116
    have h105 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1144 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1128 16 h104 kg_293_1128
    have h106 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1185 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1144 41 h105 kg_293_1144
    have h107 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1187 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1185 2 h106 kg_293_1185
    have h108 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1201 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1187 14 h107 kg_293_1187
    have h109 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1224 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1201 23 h108 kg_293_1201
    have h110 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1226 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1224 2 h109 kg_293_1224
    have h111 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1232 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1226 6 h110 kg_293_1226
    have h112 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1253 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1232 21 h111 kg_293_1232
    have h113 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1259 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1253 6 h112 kg_293_1253
    have h114 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1281 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1259 22 h113 kg_293_1259
    have h115 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1318 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1281 37 h114 kg_293_1281
    have h116 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1355 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1318 37 h115 kg_293_1318
    have h117 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1368 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1355 13 h116 kg_293_1355
    have h118 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1379 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1368 11 h117 kg_293_1368
    have h119 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1381 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1379 2 h118 kg_293_1379
    have h120 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1388 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1381 7 h119 kg_293_1381
    have h121 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1408 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1388 20 h120 kg_293_1388
    have h122 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1409 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1408 1 h121 kg_293_1408
    have h123 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1411 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1409 2 h122 kg_293_1409
    have h124 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1413 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1411 2 h123 kg_293_1411
    have h125 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1415 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1413 2 h124 kg_293_1413
    have h126 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1417 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1415 2 h125 kg_293_1415
    have h127 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1420 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1417 3 h126 kg_293_1417
    have h128 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1421 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1420 1 h127 kg_293_1420
    have h129 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1430 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1421 9 h128 kg_293_1421
    have h130 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1460 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1430 30 h129 kg_293_1430
    have h131 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1519 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1460 59 h130 kg_293_1460
    have h132 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1538 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1519 19 h131 kg_293_1519
    have h133 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1571 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1538 33 h132 kg_293_1538
    have h134 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1586 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1571 15 h133 kg_293_1571
    have h135 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1593 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1586 7 h134 kg_293_1586
    have h136 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1624 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1593 31 h135 kg_293_1593
    have h137 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1697 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1624 73 h136 kg_293_1624
    have h138 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1699 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1697 2 h137 kg_293_1697
    have h139 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1724 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1699 25 h138 kg_293_1699
    have h140 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1761 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1724 37 h139 kg_293_1724
    have h141 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1763 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1761 2 h140 kg_293_1761
    have h142 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1778 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1763 15 h141 kg_293_1763
    have h143 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1784 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1778 6 h142 kg_293_1778
    have h144 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1786 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1784 2 h143 kg_293_1784
    have h145 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1809 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1786 23 h144 kg_293_1786
    have h146 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1811 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1809 2 h145 kg_293_1809
    have h147 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1831 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1811 20 h146 kg_293_1811
    have h148 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1862 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1831 31 h147 kg_293_1831
    have h149 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1886 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1862 24 h148 kg_293_1862
    have h150 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1895 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1886 9 h149 kg_293_1886
    have h151 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1899 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1895 4 h150 kg_293_1895
    have h152 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1928 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1899 29 h151 kg_293_1899
    have h153 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1942 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1928 14 h152 kg_293_1928
    have h154 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1957 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1942 15 h153 kg_293_1942
    have h155 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1968 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1957 11 h154 kg_293_1957
    have h156 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1974 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1968 6 h155 kg_293_1968
    have h157 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1994 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1974 20 h156 kg_293_1974
    have h158 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 1998 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1994 4 h157 kg_293_1994
    have h159 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2000 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 1998 2 h158 kg_293_1998
    have h160 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2013 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2000 13 h159 kg_293_2000
    have h161 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2041 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2013 28 h160 kg_293_2013
    have h162 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2048 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2041 7 h161 kg_293_2041
    have h163 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2068 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2048 20 h162 kg_293_2048
    have h164 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2073 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2068 5 h163 kg_293_2068
    have h165 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2096 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2073 23 h164 kg_293_2073
    have h166 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2102 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2096 6 h165 kg_293_2096
    have h167 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2104 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2102 2 h166 kg_293_2102
    have h168 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2123 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2104 19 h167 kg_293_2104
    have h169 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2152 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2123 29 h168 kg_293_2123
    have h170 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2157 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2152 5 h169 kg_293_2152
    have h171 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2160 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2157 3 h170 kg_293_2157
    have h172 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2179 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2160 19 h171 kg_293_2160
    have h173 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2181 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2179 2 h172 kg_293_2179
    have h174 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2201 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2181 20 h173 kg_293_2181
    have h175 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2227 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2201 26 h174 kg_293_2201
    have h176 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2235 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2227 8 h175 kg_293_2227
    have h177 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2292 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2235 57 h176 kg_293_2235
    have h178 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2347 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2292 55 h177 kg_293_2292
    have h179 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2362 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2347 15 h178 kg_293_2347
    have h180 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2398 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2362 36 h179 kg_293_2362
    have h181 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2413 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2398 15 h180 kg_293_2398
    have h182 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2414 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2413 1 h181 kg_293_2413
    have h183 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2415 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2414 1 h182 kg_293_2414
    have h184 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2430 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2415 15 h183 kg_293_2415
    have h185 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2438 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2430 8 h184 kg_293_2430
    have h186 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2462 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2438 24 h185 kg_293_2438
    have h187 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2463 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2462 1 h186 kg_293_2462
    have h188 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2465 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2463 2 h187 kg_293_2463
    have h189 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2469 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2465 4 h188 kg_293_2465
    have h190 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2470 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2469 1 h189 kg_293_2469
    have h191 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2479 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2470 9 h190 kg_293_2470
    have h192 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2480 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2479 1 h191 kg_293_2479
    have h193 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2485 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2480 5 h192 kg_293_2480
    have h194 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2508 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2485 23 h193 kg_293_2485
    have h195 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2516 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2508 8 h194 kg_293_2508
    have h196 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2522 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2516 6 h195 kg_293_2516
    have h197 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2583 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2522 61 h196 kg_293_2522
    have h198 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2600 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2583 17 h197 kg_293_2583
    have h199 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2601 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2600 1 h198 kg_293_2600
    have h200 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2612 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2601 11 h199 kg_293_2601
    have h201 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2618 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2612 6 h200 kg_293_2612
    have h202 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2619 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2618 1 h201 kg_293_2618
    have h203 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2645 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2619 26 h202 kg_293_2619
    have h204 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2646 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2645 1 h203 kg_293_2645
    have h205 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2653 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2646 7 h204 kg_293_2646
    have h206 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2670 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2653 17 h205 kg_293_2653
    have h207 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2685 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2670 15 h206 kg_293_2670
    have h208 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2695 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2685 10 h207 kg_293_2685
    have h209 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2697 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2695 2 h208 kg_293_2695
    have h210 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2703 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2697 6 h209 kg_293_2697
    have h211 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2720 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2703 17 h210 kg_293_2703
    have h212 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2739 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2720 19 h211 kg_293_2720
    have h213 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2767 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2739 28 h212 kg_293_2739
    have h214 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2804 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2767 37 h213 kg_293_2767
    have h215 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2863 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2804 59 h214 kg_293_2804
    have h216 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2867 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2863 4 h215 kg_293_2863
    have h217 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2924 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2867 57 h216 kg_293_2867
    have h218 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2958 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2924 34 h217 kg_293_2924
    have h219 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2987 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2958 29 h218 kg_293_2958
    have h220 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2989 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2987 2 h219 kg_293_2987
    have h221 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 2995 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2989 6 h220 kg_293_2989
    have h222 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3005 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 2995 10 h221 kg_293_2995
    have h223 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3073 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3005 68 h222 kg_293_3005
    have h224 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3085 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3073 12 h223 kg_293_3073
    have h225 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3095 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3085 10 h224 kg_293_3085
    have h226 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3111 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3095 16 h225 kg_293_3095
    have h227 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3117 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3111 6 h226 kg_293_3111
    have h228 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3148 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3117 31 h227 kg_293_3117
    have h229 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3169 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3148 21 h228 kg_293_3148
    have h230 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3172 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3169 3 h229 kg_293_3169
    have h231 : IPChk.allR (Pts.glueIB K293.lits KW_293) 0 3176 = true := IPChk.allR_join (Pts.glueIB K293.lits KW_293) 0 3172 4 h230 kg_293_3172
    exact h231
  have hlen : K293.lits.length = 3176 := by decide
  intro k h1 h2
  obtain rfl : k = 293 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 293) K293.lits KW_293
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_70 : ∀ k, 294 ≤ k → k < 298 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_294 JW_294 294 4 jr_294

theorem grp6_2 : ∀ k, 287 ≤ k → k < 298 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_64
  have a1 := Pts.fa_join a0 jr6_65
  have a2 := Pts.fa_join a1 jr6_66
  have a3 := Pts.fa_join a2 jr6_67
  have a4 := Pts.fa_join a3 jr6_68
  have a5 := Pts.fa_join a4 jr6_69
  have a6 := Pts.fa_join a5 jr6_70
  exact a6

end B334.E1x.Pts.S707
