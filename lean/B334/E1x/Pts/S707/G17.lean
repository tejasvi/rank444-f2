import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J2967
import B334.E1x.Pts.S707.J2969
import B334.E1x.Pts.S707.J2973
import B334.E1x.Pts.S707.J2975
import B334.E1x.Pts.S707.J2983
import B334.E1x.Pts.S707.J2991
import B334.E1x.Pts.S707.J2999
import B334.E1x.Pts.S707.K2966L
import B334.E1x.Pts.S707.K2968L
import B334.E1x.Pts.S707.K2971L
import B334.E1x.Pts.S707.K2972L
import B334.E1x.Pts.S707.K2974L
import B334.E1x.Pts.S707.K2982L
import B334.E1x.Pts.S707.K2990L
import B334.E1x.Pts.S707.K2998L
import B334.E1x.Pts.S707.K2966Q0
import B334.E1x.Pts.S707.K2966Q1
import B334.E1x.Pts.S707.K2966Q2
import B334.E1x.Pts.S707.K2966Q3
import B334.E1x.Pts.S707.K2966Q4
import B334.E1x.Pts.S707.K2966Q5
import B334.E1x.Pts.S707.K2966Q6
import B334.E1x.Pts.S707.K2966Q7
import B334.E1x.Pts.S707.K2966Q8
import B334.E1x.Pts.S707.K2966Q9
import B334.E1x.Pts.S707.K2968Q0
import B334.E1x.Pts.S707.K2968Q1
import B334.E1x.Pts.S707.K2968Q2
import B334.E1x.Pts.S707.K2968Q3
import B334.E1x.Pts.S707.K2968Q4
import B334.E1x.Pts.S707.K2968Q5
import B334.E1x.Pts.S707.K2971Q0
import B334.E1x.Pts.S707.K2971Q1
import B334.E1x.Pts.S707.K2971Q2
import B334.E1x.Pts.S707.K2971Q3
import B334.E1x.Pts.S707.K2971Q4
import B334.E1x.Pts.S707.K2971Q5
import B334.E1x.Pts.S707.K2971Q6
import B334.E1x.Pts.S707.K2971Q7
import B334.E1x.Pts.S707.K2971Q8
import B334.E1x.Pts.S707.K2971Q9
import B334.E1x.Pts.S707.K2972Q0
import B334.E1x.Pts.S707.K2972Q1
import B334.E1x.Pts.S707.K2972Q2
import B334.E1x.Pts.S707.K2972Q3
import B334.E1x.Pts.S707.K2972Q4
import B334.E1x.Pts.S707.K2972Q5
import B334.E1x.Pts.S707.K2974Q0
import B334.E1x.Pts.S707.K2974Q1
import B334.E1x.Pts.S707.K2974Q2
import B334.E1x.Pts.S707.K2974Q3
import B334.E1x.Pts.S707.K2974Q4
import B334.E1x.Pts.S707.K2974Q5
import B334.E1x.Pts.S707.K2974Q6
import B334.E1x.Pts.S707.K2974Q7
import B334.E1x.Pts.S707.K2974Q8
import B334.E1x.Pts.S707.K2982Q0
import B334.E1x.Pts.S707.K2982Q1
import B334.E1x.Pts.S707.K2990Q0
import B334.E1x.Pts.S707.K2998Q0
import B334.E1x.Pts.S707.K2971Q10

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 2966 … 3021 (stage707_v6): the v5 Fin's job blocks r514 … r528 as
theorems, joined into `grp6_17` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_514 : ∀ k, 2966 ≤ k → k < 2967 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 958 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 2 = true := kb_2966_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 2 3 h0 kb_2966_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 5 2 h1 kb_2966_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 7 5 h2 kb_2966_7
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 12 9 h3 kb_2966_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 21 5 h4 kb_2966_21
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 26 1 h5 kb_2966_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 27 5 h6 kb_2966_27
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 32 5 h7 kb_2966_32
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 37 4 h8 kb_2966_37
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 41 7 h9 kb_2966_41
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 48 2 h10 kb_2966_48
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 65 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 50 15 h11 kb_2966_50
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 65 2 h12 kb_2966_65
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 67 6 h13 kb_2966_67
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 73 3 h14 kb_2966_73
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 76 20 h15 kb_2966_76
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 96 11 h16 kb_2966_96
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 107 18 h17 kb_2966_107
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 125 3 h18 kb_2966_125
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 128 1 h19 kb_2966_128
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 129 26 h20 kb_2966_129
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 155 5 h21 kb_2966_155
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 160 7 h22 kb_2966_160
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 167 22 h23 kb_2966_167
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 189 9 h24 kb_2966_189
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 198 31 h25 kb_2966_198
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 229 1 h26 kb_2966_229
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 230 1 h27 kb_2966_230
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 231 2 h28 kb_2966_231
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 233 14 h29 kb_2966_233
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 247 1 h30 kb_2966_247
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 248 5 h31 kb_2966_248
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 253 1 h32 kb_2966_253
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 266 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 254 12 h33 kb_2966_254
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 266 5 h34 kb_2966_266
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 271 12 h35 kb_2966_271
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 283 2 h36 kb_2966_283
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 285 13 h37 kb_2966_285
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 298 20 h38 kb_2966_298
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 318 2 h39 kb_2966_318
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 320 33 h40 kb_2966_320
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 353 2 h41 kb_2966_353
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 355 13 h42 kb_2966_355
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 368 6 h43 kb_2966_368
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 374 2 h44 kb_2966_374
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 376 27 h45 kb_2966_376
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 403 49 h46 kb_2966_403
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 452 2 h47 kb_2966_452
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 456 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 454 2 h48 kb_2966_454
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 456 10 h49 kb_2966_456
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 466 1 h50 kb_2966_466
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 467 9 h51 kb_2966_467
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 476 5 h52 kb_2966_476
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 481 1 h53 kb_2966_481
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 482 9 h54 kb_2966_482
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 491 2 h55 kb_2966_491
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 493 15 h56 kb_2966_493
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 508 1 h57 kb_2966_508
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 510 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 509 1 h58 kb_2966_509
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 510 8 h59 kb_2966_510
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 518 12 h60 kb_2966_518
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 531 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 530 1 h61 kb_2966_530
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 531 9 h62 kb_2966_531
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 543 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 540 3 h63 kb_2966_540
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 543 1 h64 kb_2966_543
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 544 8 h65 kb_2966_544
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 552 1 h66 kb_2966_552
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 553 5 h67 kb_2966_553
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 558 8 h68 kb_2966_558
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 570 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 566 4 h69 kb_2966_566
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 570 14 h70 kb_2966_570
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 584 56 h71 kb_2966_584
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 640 92 h72 kb_2966_640
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 732 26 h73 kb_2966_732
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 759 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 758 1 h74 kb_2966_758
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 760 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 759 1 h75 kb_2966_759
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 760 3 h76 kb_2966_760
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 763 8 h77 kb_2966_763
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 782 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 771 11 h78 kb_2966_771
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 782 14 h79 kb_2966_782
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 796 1 h80 kb_2966_796
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 797 1 h81 kb_2966_797
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 817 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 798 19 h82 kb_2966_798
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 817 13 h83 kb_2966_817
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 836 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 830 6 h84 kb_2966_830
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 909 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 836 73 h85 kb_2966_836
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 918 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 909 9 h86 kb_2966_909
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 918 4 h87 kb_2966_918
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 923 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 922 1 h88 kb_2966_922
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 940 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 923 17 h89 kb_2966_923
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 948 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 940 8 h90 kb_2966_940
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 948 1 h91 kb_2966_948
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 950 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 949 1 h92 kb_2966_949
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 951 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 950 1 h93 kb_2966_950
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 952 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 951 1 h94 kb_2966_951
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 953 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 952 1 h95 kb_2966_952
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 956 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 953 3 h96 kb_2966_953
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2966.lits.getD i 0)) 0 956 2 h97 kb_2966_956
    exact h98
  have hg : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 958 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 2 = true := kg_2966_0
    have h1 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 5 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 2 3 h0 kg_2966_2
    have h2 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 7 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 5 2 h1 kg_2966_5
    have h3 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 12 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 7 5 h2 kg_2966_7
    have h4 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 21 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 12 9 h3 kg_2966_12
    have h5 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 26 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 21 5 h4 kg_2966_21
    have h6 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 27 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 26 1 h5 kg_2966_26
    have h7 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 32 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 27 5 h6 kg_2966_27
    have h8 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 37 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 32 5 h7 kg_2966_32
    have h9 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 41 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 37 4 h8 kg_2966_37
    have h10 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 48 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 41 7 h9 kg_2966_41
    have h11 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 50 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 48 2 h10 kg_2966_48
    have h12 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 65 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 50 15 h11 kg_2966_50
    have h13 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 67 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 65 2 h12 kg_2966_65
    have h14 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 73 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 67 6 h13 kg_2966_67
    have h15 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 76 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 73 3 h14 kg_2966_73
    have h16 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 96 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 76 20 h15 kg_2966_76
    have h17 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 107 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 96 11 h16 kg_2966_96
    have h18 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 125 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 107 18 h17 kg_2966_107
    have h19 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 128 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 125 3 h18 kg_2966_125
    have h20 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 129 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 128 1 h19 kg_2966_128
    have h21 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 155 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 129 26 h20 kg_2966_129
    have h22 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 160 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 155 5 h21 kg_2966_155
    have h23 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 167 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 160 7 h22 kg_2966_160
    have h24 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 189 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 167 22 h23 kg_2966_167
    have h25 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 198 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 189 9 h24 kg_2966_189
    have h26 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 229 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 198 31 h25 kg_2966_198
    have h27 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 230 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 229 1 h26 kg_2966_229
    have h28 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 231 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 230 1 h27 kg_2966_230
    have h29 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 233 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 231 2 h28 kg_2966_231
    have h30 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 247 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 233 14 h29 kg_2966_233
    have h31 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 248 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 247 1 h30 kg_2966_247
    have h32 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 253 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 248 5 h31 kg_2966_248
    have h33 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 254 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 253 1 h32 kg_2966_253
    have h34 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 266 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 254 12 h33 kg_2966_254
    have h35 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 271 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 266 5 h34 kg_2966_266
    have h36 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 283 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 271 12 h35 kg_2966_271
    have h37 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 285 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 283 2 h36 kg_2966_283
    have h38 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 298 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 285 13 h37 kg_2966_285
    have h39 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 318 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 298 20 h38 kg_2966_298
    have h40 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 320 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 318 2 h39 kg_2966_318
    have h41 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 353 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 320 33 h40 kg_2966_320
    have h42 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 355 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 353 2 h41 kg_2966_353
    have h43 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 368 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 355 13 h42 kg_2966_355
    have h44 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 374 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 368 6 h43 kg_2966_368
    have h45 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 376 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 374 2 h44 kg_2966_374
    have h46 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 403 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 376 27 h45 kg_2966_376
    have h47 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 452 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 403 49 h46 kg_2966_403
    have h48 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 454 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 452 2 h47 kg_2966_452
    have h49 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 456 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 454 2 h48 kg_2966_454
    have h50 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 466 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 456 10 h49 kg_2966_456
    have h51 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 467 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 466 1 h50 kg_2966_466
    have h52 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 476 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 467 9 h51 kg_2966_467
    have h53 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 481 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 476 5 h52 kg_2966_476
    have h54 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 482 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 481 1 h53 kg_2966_481
    have h55 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 491 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 482 9 h54 kg_2966_482
    have h56 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 493 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 491 2 h55 kg_2966_491
    have h57 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 508 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 493 15 h56 kg_2966_493
    have h58 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 509 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 508 1 h57 kg_2966_508
    have h59 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 510 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 509 1 h58 kg_2966_509
    have h60 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 518 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 510 8 h59 kg_2966_510
    have h61 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 530 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 518 12 h60 kg_2966_518
    have h62 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 531 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 530 1 h61 kg_2966_530
    have h63 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 540 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 531 9 h62 kg_2966_531
    have h64 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 543 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 540 3 h63 kg_2966_540
    have h65 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 544 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 543 1 h64 kg_2966_543
    have h66 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 552 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 544 8 h65 kg_2966_544
    have h67 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 553 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 552 1 h66 kg_2966_552
    have h68 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 558 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 553 5 h67 kg_2966_553
    have h69 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 566 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 558 8 h68 kg_2966_558
    have h70 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 570 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 566 4 h69 kg_2966_566
    have h71 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 584 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 570 14 h70 kg_2966_570
    have h72 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 640 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 584 56 h71 kg_2966_584
    have h73 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 732 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 640 92 h72 kg_2966_640
    have h74 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 758 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 732 26 h73 kg_2966_732
    have h75 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 759 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 758 1 h74 kg_2966_758
    have h76 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 760 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 759 1 h75 kg_2966_759
    have h77 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 763 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 760 3 h76 kg_2966_760
    have h78 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 771 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 763 8 h77 kg_2966_763
    have h79 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 782 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 771 11 h78 kg_2966_771
    have h80 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 796 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 782 14 h79 kg_2966_782
    have h81 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 797 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 796 1 h80 kg_2966_796
    have h82 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 798 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 797 1 h81 kg_2966_797
    have h83 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 817 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 798 19 h82 kg_2966_798
    have h84 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 830 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 817 13 h83 kg_2966_817
    have h85 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 836 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 830 6 h84 kg_2966_830
    have h86 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 909 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 836 73 h85 kg_2966_836
    have h87 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 918 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 909 9 h86 kg_2966_909
    have h88 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 922 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 918 4 h87 kg_2966_918
    have h89 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 923 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 922 1 h88 kg_2966_922
    have h90 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 940 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 923 17 h89 kg_2966_923
    have h91 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 948 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 940 8 h90 kg_2966_940
    have h92 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 949 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 948 1 h91 kg_2966_948
    have h93 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 950 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 949 1 h92 kg_2966_949
    have h94 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 951 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 950 1 h93 kg_2966_950
    have h95 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 952 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 951 1 h94 kg_2966_951
    have h96 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 953 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 952 1 h95 kg_2966_952
    have h97 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 956 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 953 3 h96 kg_2966_953
    have h98 : IPChk.allR (Pts.glueIB K2966.lits KW_2966) 0 958 = true := IPChk.allR_join (Pts.glueIB K2966.lits KW_2966) 0 956 2 h97 kg_2966_956
    exact h98
  have hlen : K2966.lits.length = 958 := by decide
  intro k h1 h2
  obtain rfl : k = 2966 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2966) K2966.lits KW_2966
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_515 : ∀ k, 2967 ≤ k → k < 2968 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2967 JW_2967 2967 1 jr_2967
theorem jr6_516 : ∀ k, 2968 ≤ k → k < 2969 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 355 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 7 = true := kb_2968_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 7 1 h0 kb_2968_7
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 8 1 h1 kb_2968_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 9 1 h2 kb_2968_9
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 10 1 h3 kb_2968_10
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 11 17 h4 kb_2968_11
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 28 2 h5 kb_2968_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 30 5 h6 kb_2968_30
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 35 12 h7 kb_2968_35
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 47 1 h8 kb_2968_47
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 48 1 h9 kb_2968_48
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 49 2 h10 kb_2968_49
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 51 2 h11 kb_2968_51
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 53 2 h12 kb_2968_53
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 55 1 h13 kb_2968_55
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 56 1 h14 kb_2968_56
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 57 6 h15 kb_2968_57
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 63 3 h16 kb_2968_63
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 66 15 h17 kb_2968_66
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 81 2 h18 kb_2968_81
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 83 8 h19 kb_2968_83
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 91 6 h20 kb_2968_91
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 97 7 h21 kb_2968_97
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 104 10 h22 kb_2968_104
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 114 2 h23 kb_2968_114
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 116 1 h24 kb_2968_116
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 117 1 h25 kb_2968_117
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 118 2 h26 kb_2968_118
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 120 1 h27 kb_2968_120
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 121 2 h28 kb_2968_121
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 123 2 h29 kb_2968_123
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 125 2 h30 kb_2968_125
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 127 2 h31 kb_2968_127
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 129 2 h32 kb_2968_129
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 131 2 h33 kb_2968_131
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 133 13 h34 kb_2968_133
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 146 3 h35 kb_2968_146
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 149 7 h36 kb_2968_149
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 156 18 h37 kb_2968_156
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 174 29 h38 kb_2968_174
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 203 10 h39 kb_2968_203
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 213 15 h40 kb_2968_213
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 228 16 h41 kb_2968_228
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 244 2 h42 kb_2968_244
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 246 1 h43 kb_2968_246
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 247 16 h44 kb_2968_247
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 265 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 263 2 h45 kb_2968_263
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 265 2 h46 kb_2968_265
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 267 2 h47 kb_2968_267
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 269 3 h48 kb_2968_269
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 272 3 h49 kb_2968_272
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 275 10 h50 kb_2968_275
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 285 11 h51 kb_2968_285
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 296 41 h52 kb_2968_296
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 337 7 h53 kb_2968_337
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2968.lits.getD i 0)) 0 344 11 h54 kb_2968_344
    exact h55
  have hg : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 355 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 7 = true := kg_2968_0
    have h1 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 8 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 7 1 h0 kg_2968_7
    have h2 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 9 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 8 1 h1 kg_2968_8
    have h3 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 10 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 9 1 h2 kg_2968_9
    have h4 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 11 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 10 1 h3 kg_2968_10
    have h5 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 28 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 11 17 h4 kg_2968_11
    have h6 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 30 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 28 2 h5 kg_2968_28
    have h7 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 35 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 30 5 h6 kg_2968_30
    have h8 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 47 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 35 12 h7 kg_2968_35
    have h9 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 48 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 47 1 h8 kg_2968_47
    have h10 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 49 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 48 1 h9 kg_2968_48
    have h11 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 51 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 49 2 h10 kg_2968_49
    have h12 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 53 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 51 2 h11 kg_2968_51
    have h13 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 55 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 53 2 h12 kg_2968_53
    have h14 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 56 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 55 1 h13 kg_2968_55
    have h15 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 57 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 56 1 h14 kg_2968_56
    have h16 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 63 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 57 6 h15 kg_2968_57
    have h17 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 66 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 63 3 h16 kg_2968_63
    have h18 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 81 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 66 15 h17 kg_2968_66
    have h19 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 83 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 81 2 h18 kg_2968_81
    have h20 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 91 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 83 8 h19 kg_2968_83
    have h21 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 97 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 91 6 h20 kg_2968_91
    have h22 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 104 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 97 7 h21 kg_2968_97
    have h23 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 114 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 104 10 h22 kg_2968_104
    have h24 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 116 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 114 2 h23 kg_2968_114
    have h25 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 117 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 116 1 h24 kg_2968_116
    have h26 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 118 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 117 1 h25 kg_2968_117
    have h27 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 120 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 118 2 h26 kg_2968_118
    have h28 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 121 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 120 1 h27 kg_2968_120
    have h29 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 123 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 121 2 h28 kg_2968_121
    have h30 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 125 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 123 2 h29 kg_2968_123
    have h31 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 127 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 125 2 h30 kg_2968_125
    have h32 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 129 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 127 2 h31 kg_2968_127
    have h33 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 131 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 129 2 h32 kg_2968_129
    have h34 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 133 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 131 2 h33 kg_2968_131
    have h35 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 146 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 133 13 h34 kg_2968_133
    have h36 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 149 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 146 3 h35 kg_2968_146
    have h37 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 156 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 149 7 h36 kg_2968_149
    have h38 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 174 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 156 18 h37 kg_2968_156
    have h39 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 203 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 174 29 h38 kg_2968_174
    have h40 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 213 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 203 10 h39 kg_2968_203
    have h41 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 228 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 213 15 h40 kg_2968_213
    have h42 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 244 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 228 16 h41 kg_2968_228
    have h43 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 246 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 244 2 h42 kg_2968_244
    have h44 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 247 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 246 1 h43 kg_2968_246
    have h45 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 263 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 247 16 h44 kg_2968_247
    have h46 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 265 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 263 2 h45 kg_2968_263
    have h47 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 267 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 265 2 h46 kg_2968_265
    have h48 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 269 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 267 2 h47 kg_2968_267
    have h49 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 272 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 269 3 h48 kg_2968_269
    have h50 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 275 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 272 3 h49 kg_2968_272
    have h51 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 285 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 275 10 h50 kg_2968_275
    have h52 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 296 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 285 11 h51 kg_2968_285
    have h53 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 337 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 296 41 h52 kg_2968_296
    have h54 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 344 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 337 7 h53 kg_2968_337
    have h55 : IPChk.allR (Pts.glueIB K2968.lits KW_2968) 0 355 = true := IPChk.allR_join (Pts.glueIB K2968.lits KW_2968) 0 344 11 h54 kg_2968_344
    exact h55
  have hlen : K2968.lits.length = 355 := by decide
  intro k h1 h2
  obtain rfl : k = 2968 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2968) K2968.lits KW_2968
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_517 : ∀ k, 2969 ≤ k → k < 2971 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2969 JW_2969 2969 2 jr_2969
theorem jr6_518 : ∀ k, 2971 ≤ k → k < 2972 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1244 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 3 = true := kb_2971_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 3 8 h0 kb_2971_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 11 8 h1 kb_2971_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 19 2 h2 kb_2971_19
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 21 8 h3 kb_2971_21
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 29 8 h4 kb_2971_29
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 37 1 h5 kb_2971_37
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 38 11 h6 kb_2971_38
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 49 18 h7 kb_2971_49
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 67 2 h8 kb_2971_67
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 69 6 h9 kb_2971_69
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 75 2 h10 kb_2971_75
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 77 22 h11 kb_2971_77
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 99 2 h12 kb_2971_99
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 101 2 h13 kb_2971_101
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 103 6 h14 kb_2971_103
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 109 2 h15 kb_2971_109
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 111 20 h16 kb_2971_111
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 131 4 h17 kb_2971_131
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 135 1 h18 kb_2971_135
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 136 1 h19 kb_2971_136
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 137 22 h20 kb_2971_137
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 159 9 h21 kb_2971_159
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 168 6 h22 kb_2971_168
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 174 2 h23 kb_2971_174
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 176 18 h24 kb_2971_176
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 194 29 h25 kb_2971_194
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 223 25 h26 kb_2971_223
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 248 9 h27 kb_2971_248
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 257 25 h28 kb_2971_257
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 282 25 h29 kb_2971_282
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 307 22 h30 kb_2971_307
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 329 2 h31 kb_2971_329
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 331 14 h32 kb_2971_331
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 345 2 h33 kb_2971_345
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 347 6 h34 kb_2971_347
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 353 2 h35 kb_2971_353
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 355 20 h36 kb_2971_355
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 375 8 h37 kb_2971_375
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 383 2 h38 kb_2971_383
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 385 20 h39 kb_2971_385
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 405 2 h40 kb_2971_405
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 407 20 h41 kb_2971_407
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 427 20 h42 kb_2971_427
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 447 2 h43 kb_2971_447
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 449 33 h44 kb_2971_449
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 482 1 h45 kb_2971_482
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 483 2 h46 kb_2971_483
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 485 4 h47 kb_2971_485
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 501 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 489 12 h48 kb_2971_489
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 501 2 h49 kb_2971_501
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 503 20 h50 kb_2971_503
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 523 2 h51 kb_2971_523
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 525 12 h52 kb_2971_525
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 537 3 h53 kb_2971_537
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 540 7 h54 kb_2971_540
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 547 12 h55 kb_2971_547
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 568 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 559 9 h56 kb_2971_559
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 570 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 568 2 h57 kb_2971_568
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 570 13 h58 kb_2971_570
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 583 13 h59 kb_2971_583
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 596 28 h60 kb_2971_596
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 624 2 h61 kb_2971_624
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 632 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 626 6 h62 kb_2971_626
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 651 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 632 19 h63 kb_2971_632
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 651 2 h64 kb_2971_651
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 653 2 h65 kb_2971_653
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 655 32 h66 kb_2971_655
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 687 28 h67 kb_2971_687
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 721 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 715 6 h68 kb_2971_715
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 721 2 h69 kb_2971_721
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 723 19 h70 kb_2971_723
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 750 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 742 8 h71 kb_2971_742
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 768 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 750 18 h72 kb_2971_750
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 774 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 768 6 h73 kb_2971_768
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 776 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 774 2 h74 kb_2971_774
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 776 18 h75 kb_2971_776
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 794 28 h76 kb_2971_794
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 822 2 h77 kb_2971_822
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 838 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 824 14 h78 kb_2971_824
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 838 4 h79 kb_2971_838
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 865 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 842 23 h80 kb_2971_842
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 865 2 h81 kb_2971_865
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 873 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 867 6 h82 kb_2971_867
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 873 5 h83 kb_2971_873
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 888 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 878 10 h84 kb_2971_878
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 890 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 888 2 h85 kb_2971_888
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 892 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 890 2 h86 kb_2971_890
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 913 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 892 21 h87 kb_2971_892
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 939 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 913 26 h88 kb_2971_913
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 952 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 939 13 h89 kb_2971_939
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 952 2 h90 kb_2971_952
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 966 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 954 12 h91 kb_2971_954
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 966 8 h92 kb_2971_966
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 992 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 974 18 h93 kb_2971_974
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 992 2 h94 kb_2971_992
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1007 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 994 13 h95 kb_2971_994
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1021 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1007 14 h96 kb_2971_1007
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1021 7 h97 kb_2971_1021
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1057 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1028 29 h98 kb_2971_1028
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1057 11 h99 kb_2971_1057
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1068 33 h100 kb_2971_1068
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1101 31 h101 kb_2971_1101
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1132 1 h102 kb_2971_1132
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1133 25 h103 kb_2971_1133
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1158 25 h104 kb_2971_1158
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1183 3 h105 kb_2971_1183
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1186 7 h106 kb_2971_1186
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1193 25 h107 kb_2971_1193
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1218 3 h108 kb_2971_1218
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2971.lits.getD i 0)) 0 1221 23 h109 kb_2971_1221
    exact h110
  have hg : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1244 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 3 = true := kg_2971_0
    have h1 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 11 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 3 8 h0 kg_2971_3
    have h2 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 19 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 11 8 h1 kg_2971_11
    have h3 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 21 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 19 2 h2 kg_2971_19
    have h4 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 29 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 21 8 h3 kg_2971_21
    have h5 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 37 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 29 8 h4 kg_2971_29
    have h6 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 38 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 37 1 h5 kg_2971_37
    have h7 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 49 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 38 11 h6 kg_2971_38
    have h8 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 67 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 49 18 h7 kg_2971_49
    have h9 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 69 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 67 2 h8 kg_2971_67
    have h10 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 75 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 69 6 h9 kg_2971_69
    have h11 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 77 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 75 2 h10 kg_2971_75
    have h12 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 99 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 77 22 h11 kg_2971_77
    have h13 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 101 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 99 2 h12 kg_2971_99
    have h14 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 103 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 101 2 h13 kg_2971_101
    have h15 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 109 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 103 6 h14 kg_2971_103
    have h16 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 111 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 109 2 h15 kg_2971_109
    have h17 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 131 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 111 20 h16 kg_2971_111
    have h18 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 135 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 131 4 h17 kg_2971_131
    have h19 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 136 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 135 1 h18 kg_2971_135
    have h20 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 137 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 136 1 h19 kg_2971_136
    have h21 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 159 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 137 22 h20 kg_2971_137
    have h22 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 168 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 159 9 h21 kg_2971_159
    have h23 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 174 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 168 6 h22 kg_2971_168
    have h24 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 176 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 174 2 h23 kg_2971_174
    have h25 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 194 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 176 18 h24 kg_2971_176
    have h26 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 223 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 194 29 h25 kg_2971_194
    have h27 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 248 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 223 25 h26 kg_2971_223
    have h28 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 257 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 248 9 h27 kg_2971_248
    have h29 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 282 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 257 25 h28 kg_2971_257
    have h30 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 307 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 282 25 h29 kg_2971_282
    have h31 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 329 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 307 22 h30 kg_2971_307
    have h32 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 331 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 329 2 h31 kg_2971_329
    have h33 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 345 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 331 14 h32 kg_2971_331
    have h34 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 347 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 345 2 h33 kg_2971_345
    have h35 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 353 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 347 6 h34 kg_2971_347
    have h36 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 355 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 353 2 h35 kg_2971_353
    have h37 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 375 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 355 20 h36 kg_2971_355
    have h38 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 383 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 375 8 h37 kg_2971_375
    have h39 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 385 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 383 2 h38 kg_2971_383
    have h40 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 405 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 385 20 h39 kg_2971_385
    have h41 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 407 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 405 2 h40 kg_2971_405
    have h42 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 427 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 407 20 h41 kg_2971_407
    have h43 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 447 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 427 20 h42 kg_2971_427
    have h44 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 449 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 447 2 h43 kg_2971_447
    have h45 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 482 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 449 33 h44 kg_2971_449
    have h46 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 483 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 482 1 h45 kg_2971_482
    have h47 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 485 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 483 2 h46 kg_2971_483
    have h48 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 489 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 485 4 h47 kg_2971_485
    have h49 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 501 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 489 12 h48 kg_2971_489
    have h50 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 503 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 501 2 h49 kg_2971_501
    have h51 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 523 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 503 20 h50 kg_2971_503
    have h52 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 525 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 523 2 h51 kg_2971_523
    have h53 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 537 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 525 12 h52 kg_2971_525
    have h54 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 540 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 537 3 h53 kg_2971_537
    have h55 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 547 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 540 7 h54 kg_2971_540
    have h56 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 559 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 547 12 h55 kg_2971_547
    have h57 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 568 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 559 9 h56 kg_2971_559
    have h58 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 570 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 568 2 h57 kg_2971_568
    have h59 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 583 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 570 13 h58 kg_2971_570
    have h60 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 596 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 583 13 h59 kg_2971_583
    have h61 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 624 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 596 28 h60 kg_2971_596
    have h62 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 626 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 624 2 h61 kg_2971_624
    have h63 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 632 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 626 6 h62 kg_2971_626
    have h64 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 651 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 632 19 h63 kg_2971_632
    have h65 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 653 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 651 2 h64 kg_2971_651
    have h66 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 655 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 653 2 h65 kg_2971_653
    have h67 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 687 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 655 32 h66 kg_2971_655
    have h68 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 715 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 687 28 h67 kg_2971_687
    have h69 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 721 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 715 6 h68 kg_2971_715
    have h70 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 723 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 721 2 h69 kg_2971_721
    have h71 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 742 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 723 19 h70 kg_2971_723
    have h72 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 750 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 742 8 h71 kg_2971_742
    have h73 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 768 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 750 18 h72 kg_2971_750
    have h74 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 774 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 768 6 h73 kg_2971_768
    have h75 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 776 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 774 2 h74 kg_2971_774
    have h76 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 794 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 776 18 h75 kg_2971_776
    have h77 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 822 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 794 28 h76 kg_2971_794
    have h78 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 824 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 822 2 h77 kg_2971_822
    have h79 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 838 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 824 14 h78 kg_2971_824
    have h80 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 842 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 838 4 h79 kg_2971_838
    have h81 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 865 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 842 23 h80 kg_2971_842
    have h82 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 867 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 865 2 h81 kg_2971_865
    have h83 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 873 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 867 6 h82 kg_2971_867
    have h84 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 878 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 873 5 h83 kg_2971_873
    have h85 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 888 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 878 10 h84 kg_2971_878
    have h86 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 890 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 888 2 h85 kg_2971_888
    have h87 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 892 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 890 2 h86 kg_2971_890
    have h88 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 913 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 892 21 h87 kg_2971_892
    have h89 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 939 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 913 26 h88 kg_2971_913
    have h90 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 952 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 939 13 h89 kg_2971_939
    have h91 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 954 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 952 2 h90 kg_2971_952
    have h92 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 966 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 954 12 h91 kg_2971_954
    have h93 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 974 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 966 8 h92 kg_2971_966
    have h94 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 992 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 974 18 h93 kg_2971_974
    have h95 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 994 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 992 2 h94 kg_2971_992
    have h96 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1007 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 994 13 h95 kg_2971_994
    have h97 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1021 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1007 14 h96 kg_2971_1007
    have h98 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1028 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1021 7 h97 kg_2971_1021
    have h99 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1057 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1028 29 h98 kg_2971_1028
    have h100 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1068 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1057 11 h99 kg_2971_1057
    have h101 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1101 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1068 33 h100 kg_2971_1068
    have h102 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1132 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1101 31 h101 kg_2971_1101
    have h103 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1133 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1132 1 h102 kg_2971_1132
    have h104 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1158 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1133 25 h103 kg_2971_1133
    have h105 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1183 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1158 25 h104 kg_2971_1158
    have h106 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1186 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1183 3 h105 kg_2971_1183
    have h107 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1193 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1186 7 h106 kg_2971_1186
    have h108 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1218 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1193 25 h107 kg_2971_1193
    have h109 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1221 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1218 3 h108 kg_2971_1218
    have h110 : IPChk.allR (Pts.glueIB K2971.lits KW_2971) 0 1244 = true := IPChk.allR_join (Pts.glueIB K2971.lits KW_2971) 0 1221 23 h109 kg_2971_1221
    exact h110
  have hlen : K2971.lits.length = 1244 := by decide
  intro k h1 h2
  obtain rfl : k = 2971 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2971) K2971.lits KW_2971
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_519 : ∀ k, 2972 ≤ k → k < 2973 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 588 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 2 = true := kb_2972_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 2 8 h0 kb_2972_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 10 8 h1 kb_2972_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 18 2 h2 kb_2972_18
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 20 1 h3 kb_2972_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 21 16 h4 kb_2972_21
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 37 15 h5 kb_2972_37
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 52 6 h6 kb_2972_52
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 58 2 h7 kb_2972_58
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 60 19 h8 kb_2972_60
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 79 1 h9 kb_2972_79
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 80 2 h10 kb_2972_80
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 82 8 h11 kb_2972_82
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 90 2 h12 kb_2972_90
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 92 20 h13 kb_2972_92
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 112 1 h14 kb_2972_112
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 113 2 h15 kb_2972_113
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 115 1 h16 kb_2972_115
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 116 9 h17 kb_2972_116
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 125 4 h18 kb_2972_125
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 129 22 h19 kb_2972_129
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 151 22 h20 kb_2972_151
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 173 7 h21 kb_2972_173
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 180 12 h22 kb_2972_180
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 192 2 h23 kb_2972_192
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 194 6 h24 kb_2972_194
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 200 2 h25 kb_2972_200
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 202 14 h26 kb_2972_202
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 216 3 h27 kb_2972_216
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 219 7 h28 kb_2972_219
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 226 2 h29 kb_2972_226
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 228 12 h30 kb_2972_228
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 240 1 h31 kb_2972_240
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 241 9 h32 kb_2972_241
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 250 6 h33 kb_2972_250
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 256 14 h34 kb_2972_256
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 270 4 h35 kb_2972_270
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 274 18 h36 kb_2972_274
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 292 14 h37 kb_2972_292
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 306 3 h38 kb_2972_306
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 309 6 h39 kb_2972_309
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 315 13 h40 kb_2972_315
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 328 2 h41 kb_2972_328
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 330 2 h42 kb_2972_330
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 332 31 h43 kb_2972_332
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 363 15 h44 kb_2972_363
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 378 2 h45 kb_2972_378
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 380 13 h46 kb_2972_380
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 393 8 h47 kb_2972_393
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 401 12 h48 kb_2972_401
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 413 6 h49 kb_2972_413
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 419 2 h50 kb_2972_419
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 421 13 h51 kb_2972_421
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 434 18 h52 kb_2972_434
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 452 2 h53 kb_2972_452
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 454 12 h54 kb_2972_454
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 466 23 h55 kb_2972_466
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 489 10 h56 kb_2972_489
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 499 8 h57 kb_2972_499
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 507 31 h58 kb_2972_507
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 538 16 h59 kb_2972_538
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 570 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 554 16 h60 kb_2972_554
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2972.lits.getD i 0)) 0 570 18 h61 kb_2972_570
    exact h62
  have hg : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 588 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 2 = true := kg_2972_0
    have h1 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 10 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 2 8 h0 kg_2972_2
    have h2 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 18 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 10 8 h1 kg_2972_10
    have h3 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 20 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 18 2 h2 kg_2972_18
    have h4 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 21 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 20 1 h3 kg_2972_20
    have h5 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 37 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 21 16 h4 kg_2972_21
    have h6 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 52 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 37 15 h5 kg_2972_37
    have h7 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 58 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 52 6 h6 kg_2972_52
    have h8 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 60 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 58 2 h7 kg_2972_58
    have h9 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 79 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 60 19 h8 kg_2972_60
    have h10 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 80 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 79 1 h9 kg_2972_79
    have h11 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 82 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 80 2 h10 kg_2972_80
    have h12 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 90 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 82 8 h11 kg_2972_82
    have h13 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 92 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 90 2 h12 kg_2972_90
    have h14 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 112 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 92 20 h13 kg_2972_92
    have h15 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 113 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 112 1 h14 kg_2972_112
    have h16 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 115 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 113 2 h15 kg_2972_113
    have h17 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 116 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 115 1 h16 kg_2972_115
    have h18 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 125 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 116 9 h17 kg_2972_116
    have h19 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 129 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 125 4 h18 kg_2972_125
    have h20 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 151 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 129 22 h19 kg_2972_129
    have h21 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 173 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 151 22 h20 kg_2972_151
    have h22 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 180 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 173 7 h21 kg_2972_173
    have h23 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 192 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 180 12 h22 kg_2972_180
    have h24 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 194 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 192 2 h23 kg_2972_192
    have h25 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 200 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 194 6 h24 kg_2972_194
    have h26 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 202 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 200 2 h25 kg_2972_200
    have h27 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 216 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 202 14 h26 kg_2972_202
    have h28 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 219 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 216 3 h27 kg_2972_216
    have h29 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 226 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 219 7 h28 kg_2972_219
    have h30 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 228 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 226 2 h29 kg_2972_226
    have h31 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 240 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 228 12 h30 kg_2972_228
    have h32 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 241 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 240 1 h31 kg_2972_240
    have h33 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 250 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 241 9 h32 kg_2972_241
    have h34 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 256 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 250 6 h33 kg_2972_250
    have h35 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 270 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 256 14 h34 kg_2972_256
    have h36 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 274 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 270 4 h35 kg_2972_270
    have h37 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 292 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 274 18 h36 kg_2972_274
    have h38 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 306 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 292 14 h37 kg_2972_292
    have h39 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 309 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 306 3 h38 kg_2972_306
    have h40 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 315 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 309 6 h39 kg_2972_309
    have h41 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 328 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 315 13 h40 kg_2972_315
    have h42 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 330 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 328 2 h41 kg_2972_328
    have h43 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 332 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 330 2 h42 kg_2972_330
    have h44 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 363 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 332 31 h43 kg_2972_332
    have h45 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 378 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 363 15 h44 kg_2972_363
    have h46 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 380 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 378 2 h45 kg_2972_378
    have h47 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 393 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 380 13 h46 kg_2972_380
    have h48 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 401 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 393 8 h47 kg_2972_393
    have h49 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 413 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 401 12 h48 kg_2972_401
    have h50 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 419 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 413 6 h49 kg_2972_413
    have h51 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 421 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 419 2 h50 kg_2972_419
    have h52 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 434 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 421 13 h51 kg_2972_421
    have h53 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 452 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 434 18 h52 kg_2972_434
    have h54 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 454 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 452 2 h53 kg_2972_452
    have h55 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 466 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 454 12 h54 kg_2972_454
    have h56 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 489 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 466 23 h55 kg_2972_466
    have h57 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 499 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 489 10 h56 kg_2972_489
    have h58 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 507 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 499 8 h57 kg_2972_499
    have h59 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 538 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 507 31 h58 kg_2972_507
    have h60 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 554 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 538 16 h59 kg_2972_538
    have h61 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 570 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 554 16 h60 kg_2972_554
    have h62 : IPChk.allR (Pts.glueIB K2972.lits KW_2972) 0 588 = true := IPChk.allR_join (Pts.glueIB K2972.lits KW_2972) 0 570 18 h61 kg_2972_570
    exact h62
  have hlen : K2972.lits.length = 588 := by decide
  intro k h1 h2
  obtain rfl : k = 2972 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2972) K2972.lits KW_2972
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_520 : ∀ k, 2973 ≤ k → k < 2974 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2973 JW_2973 2973 1 jr_2973
theorem jr6_521 : ∀ k, 2974 ≤ k → k < 2975 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 800 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 1 = true := kb_2974_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 1 1 h0 kb_2974_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 2 1 h1 kb_2974_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 3 17 h2 kb_2974_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 20 14 h3 kb_2974_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 34 6 h4 kb_2974_34
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 40 2 h5 kb_2974_40
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 42 22 h6 kb_2974_42
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 65 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 64 1 h7 kb_2974_64
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 65 1 h8 kb_2974_65
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 66 1 h9 kb_2974_66
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 67 1 h10 kb_2974_67
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 68 2 h11 kb_2974_68
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 70 2 h12 kb_2974_70
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 72 12 h13 kb_2974_72
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 84 4 h14 kb_2974_84
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 88 25 h15 kb_2974_88
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 113 2 h16 kb_2974_113
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 115 14 h17 kb_2974_115
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 129 6 h18 kb_2974_129
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 135 11 h19 kb_2974_135
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 146 14 h20 kb_2974_146
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 160 2 h21 kb_2974_160
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 162 6 h22 kb_2974_162
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 168 2 h23 kb_2974_168
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 170 22 h24 kb_2974_170
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 192 1 h25 kb_2974_192
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 193 2 h26 kb_2974_193
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 195 3 h27 kb_2974_195
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 198 6 h28 kb_2974_198
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 204 2 h29 kb_2974_204
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 206 20 h30 kb_2974_206
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 226 1 h31 kb_2974_226
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 227 1 h32 kb_2974_227
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 228 3 h33 kb_2974_228
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 231 20 h34 kb_2974_231
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 251 1 h35 kb_2974_251
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 252 1 h36 kb_2974_252
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 253 18 h37 kb_2974_253
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 271 3 h38 kb_2974_271
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 274 2 h39 kb_2974_274
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 276 2 h40 kb_2974_276
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 278 1 h41 kb_2974_278
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 279 2 h42 kb_2974_279
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 281 3 h43 kb_2974_281
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 284 21 h44 kb_2974_284
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 305 2 h45 kb_2974_305
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 307 6 h46 kb_2974_307
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 313 21 h47 kb_2974_313
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 336 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 334 2 h48 kb_2974_334
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 336 4 h49 kb_2974_336
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 340 45 h50 kb_2974_340
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 385 18 h51 kb_2974_385
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 403 25 h52 kb_2974_403
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 428 6 h53 kb_2974_428
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 434 13 h54 kb_2974_434
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 458 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 447 11 h55 kb_2974_447
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 458 7 h56 kb_2974_458
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 465 20 h57 kb_2974_465
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 485 1 h58 kb_2974_485
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 486 1 h59 kb_2974_486
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 487 6 h60 kb_2974_487
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 493 2 h61 kb_2974_493
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 495 19 h62 kb_2974_495
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 541 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 514 27 h63 kb_2974_514
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 541 6 h64 kb_2974_541
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 547 1 h65 kb_2974_547
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 548 2 h66 kb_2974_548
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 550 3 h67 kb_2974_550
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 553 5 h68 kb_2974_553
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 558 15 h69 kb_2974_558
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 573 3 h70 kb_2974_573
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 576 15 h71 kb_2974_576
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 604 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 591 13 h72 kb_2974_591
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 604 2 h73 kb_2974_604
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 606 2 h74 kb_2974_606
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 608 3 h75 kb_2974_608
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 611 43 h76 kb_2974_611
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 654 61 h77 kb_2974_654
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 715 4 h78 kb_2974_715
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 746 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 719 27 h79 kb_2974_719
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 749 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 746 3 h80 kb_2974_746
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 749 7 h81 kb_2974_749
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 756 30 h82 kb_2974_756
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 800 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2974.lits.getD i 0)) 0 786 14 h83 kb_2974_786
    exact h84
  have hg : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 800 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 1 = true := kg_2974_0
    have h1 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 2 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 1 1 h0 kg_2974_1
    have h2 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 3 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 2 1 h1 kg_2974_2
    have h3 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 20 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 3 17 h2 kg_2974_3
    have h4 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 34 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 20 14 h3 kg_2974_20
    have h5 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 40 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 34 6 h4 kg_2974_34
    have h6 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 42 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 40 2 h5 kg_2974_40
    have h7 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 64 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 42 22 h6 kg_2974_42
    have h8 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 65 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 64 1 h7 kg_2974_64
    have h9 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 66 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 65 1 h8 kg_2974_65
    have h10 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 67 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 66 1 h9 kg_2974_66
    have h11 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 68 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 67 1 h10 kg_2974_67
    have h12 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 70 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 68 2 h11 kg_2974_68
    have h13 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 72 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 70 2 h12 kg_2974_70
    have h14 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 84 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 72 12 h13 kg_2974_72
    have h15 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 88 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 84 4 h14 kg_2974_84
    have h16 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 113 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 88 25 h15 kg_2974_88
    have h17 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 115 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 113 2 h16 kg_2974_113
    have h18 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 129 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 115 14 h17 kg_2974_115
    have h19 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 135 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 129 6 h18 kg_2974_129
    have h20 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 146 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 135 11 h19 kg_2974_135
    have h21 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 160 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 146 14 h20 kg_2974_146
    have h22 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 162 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 160 2 h21 kg_2974_160
    have h23 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 168 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 162 6 h22 kg_2974_162
    have h24 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 170 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 168 2 h23 kg_2974_168
    have h25 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 192 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 170 22 h24 kg_2974_170
    have h26 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 193 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 192 1 h25 kg_2974_192
    have h27 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 195 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 193 2 h26 kg_2974_193
    have h28 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 198 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 195 3 h27 kg_2974_195
    have h29 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 204 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 198 6 h28 kg_2974_198
    have h30 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 206 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 204 2 h29 kg_2974_204
    have h31 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 226 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 206 20 h30 kg_2974_206
    have h32 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 227 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 226 1 h31 kg_2974_226
    have h33 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 228 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 227 1 h32 kg_2974_227
    have h34 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 231 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 228 3 h33 kg_2974_228
    have h35 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 251 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 231 20 h34 kg_2974_231
    have h36 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 252 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 251 1 h35 kg_2974_251
    have h37 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 253 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 252 1 h36 kg_2974_252
    have h38 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 271 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 253 18 h37 kg_2974_253
    have h39 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 274 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 271 3 h38 kg_2974_271
    have h40 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 276 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 274 2 h39 kg_2974_274
    have h41 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 278 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 276 2 h40 kg_2974_276
    have h42 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 279 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 278 1 h41 kg_2974_278
    have h43 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 281 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 279 2 h42 kg_2974_279
    have h44 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 284 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 281 3 h43 kg_2974_281
    have h45 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 305 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 284 21 h44 kg_2974_284
    have h46 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 307 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 305 2 h45 kg_2974_305
    have h47 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 313 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 307 6 h46 kg_2974_307
    have h48 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 334 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 313 21 h47 kg_2974_313
    have h49 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 336 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 334 2 h48 kg_2974_334
    have h50 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 340 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 336 4 h49 kg_2974_336
    have h51 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 385 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 340 45 h50 kg_2974_340
    have h52 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 403 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 385 18 h51 kg_2974_385
    have h53 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 428 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 403 25 h52 kg_2974_403
    have h54 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 434 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 428 6 h53 kg_2974_428
    have h55 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 447 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 434 13 h54 kg_2974_434
    have h56 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 458 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 447 11 h55 kg_2974_447
    have h57 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 465 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 458 7 h56 kg_2974_458
    have h58 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 485 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 465 20 h57 kg_2974_465
    have h59 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 486 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 485 1 h58 kg_2974_485
    have h60 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 487 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 486 1 h59 kg_2974_486
    have h61 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 493 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 487 6 h60 kg_2974_487
    have h62 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 495 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 493 2 h61 kg_2974_493
    have h63 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 514 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 495 19 h62 kg_2974_495
    have h64 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 541 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 514 27 h63 kg_2974_514
    have h65 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 547 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 541 6 h64 kg_2974_541
    have h66 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 548 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 547 1 h65 kg_2974_547
    have h67 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 550 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 548 2 h66 kg_2974_548
    have h68 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 553 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 550 3 h67 kg_2974_550
    have h69 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 558 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 553 5 h68 kg_2974_553
    have h70 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 573 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 558 15 h69 kg_2974_558
    have h71 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 576 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 573 3 h70 kg_2974_573
    have h72 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 591 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 576 15 h71 kg_2974_576
    have h73 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 604 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 591 13 h72 kg_2974_591
    have h74 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 606 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 604 2 h73 kg_2974_604
    have h75 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 608 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 606 2 h74 kg_2974_606
    have h76 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 611 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 608 3 h75 kg_2974_608
    have h77 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 654 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 611 43 h76 kg_2974_611
    have h78 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 715 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 654 61 h77 kg_2974_654
    have h79 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 719 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 715 4 h78 kg_2974_715
    have h80 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 746 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 719 27 h79 kg_2974_719
    have h81 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 749 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 746 3 h80 kg_2974_746
    have h82 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 756 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 749 7 h81 kg_2974_749
    have h83 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 786 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 756 30 h82 kg_2974_756
    have h84 : IPChk.allR (Pts.glueIB K2974.lits KW_2974) 0 800 = true := IPChk.allR_join (Pts.glueIB K2974.lits KW_2974) 0 786 14 h83 kg_2974_786
    exact h84
  have hlen : K2974.lits.length = 800 := by decide
  intro k h1 h2
  obtain rfl : k = 2974 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2974) K2974.lits KW_2974
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_522 : ∀ k, 2975 ≤ k → k < 2982 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2975 JW_2975 2975 7 jr_2975
theorem jr6_523 : ∀ k, 2982 ≤ k → k < 2983 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 100 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 2 = true := kb_2982_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 2 6 h0 kb_2982_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 8 2 h1 kb_2982_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 10 22 h2 kb_2982_10
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 32 1 h3 kb_2982_32
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 33 1 h4 kb_2982_33
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 34 2 h5 kb_2982_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 36 2 h6 kb_2982_36
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 38 4 h7 kb_2982_38
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 42 22 h8 kb_2982_42
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 64 5 h9 kb_2982_64
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 69 2 h10 kb_2982_69
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 71 2 h11 kb_2982_71
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 73 2 h12 kb_2982_73
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 75 2 h13 kb_2982_75
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 77 16 h14 kb_2982_77
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 93 1 h15 kb_2982_93
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 94 1 h16 kb_2982_94
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 95 2 h17 kb_2982_95
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2982.lits.getD i 0)) 0 97 3 h18 kb_2982_97
    exact h19
  have hg : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 100 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 2 = true := kg_2982_0
    have h1 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 8 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 2 6 h0 kg_2982_2
    have h2 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 10 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 8 2 h1 kg_2982_8
    have h3 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 32 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 10 22 h2 kg_2982_10
    have h4 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 33 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 32 1 h3 kg_2982_32
    have h5 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 34 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 33 1 h4 kg_2982_33
    have h6 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 36 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 34 2 h5 kg_2982_34
    have h7 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 38 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 36 2 h6 kg_2982_36
    have h8 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 42 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 38 4 h7 kg_2982_38
    have h9 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 64 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 42 22 h8 kg_2982_42
    have h10 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 69 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 64 5 h9 kg_2982_64
    have h11 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 71 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 69 2 h10 kg_2982_69
    have h12 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 73 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 71 2 h11 kg_2982_71
    have h13 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 75 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 73 2 h12 kg_2982_73
    have h14 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 77 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 75 2 h13 kg_2982_75
    have h15 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 93 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 77 16 h14 kg_2982_77
    have h16 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 94 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 93 1 h15 kg_2982_93
    have h17 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 95 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 94 1 h16 kg_2982_94
    have h18 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 97 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 95 2 h17 kg_2982_95
    have h19 : IPChk.allR (Pts.glueIB K2982.lits KW_2982) 0 100 = true := IPChk.allR_join (Pts.glueIB K2982.lits KW_2982) 0 97 3 h18 kg_2982_97
    exact h19
  have hlen : K2982.lits.length = 100 := by decide
  intro k h1 h2
  obtain rfl : k = 2982 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2982) K2982.lits KW_2982
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_524 : ∀ k, 2983 ≤ k → k < 2990 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2983 JW_2983 2983 7 jr_2983
theorem jr6_525 : ∀ k, 2990 ≤ k → k < 2991 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 5 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 1 = true := kb_2990_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 1 2 h0 kb_2990_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2990.lits.getD i 0)) 0 3 2 h1 kb_2990_3
    exact h2
  have hg : IPChk.allR (Pts.glueIB K2990.lits KW_2990) 0 5 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2990.lits KW_2990) 0 1 = true := kg_2990_0
    have h1 : IPChk.allR (Pts.glueIB K2990.lits KW_2990) 0 3 = true := IPChk.allR_join (Pts.glueIB K2990.lits KW_2990) 0 1 2 h0 kg_2990_1
    have h2 : IPChk.allR (Pts.glueIB K2990.lits KW_2990) 0 5 = true := IPChk.allR_join (Pts.glueIB K2990.lits KW_2990) 0 3 2 h1 kg_2990_3
    exact h2
  have hlen : K2990.lits.length = 5 := by decide
  intro k h1 h2
  obtain rfl : k = 2990 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2990) K2990.lits KW_2990
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_526 : ∀ k, 2991 ≤ k → k < 2998 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2991 JW_2991 2991 7 jr_2991
theorem jr6_527 : ∀ k, 2998 ≤ k → k < 2999 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2998.lits.getD i 0)) 0 2 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2998.lits.getD i 0)) 0 1 = true := kb_2998_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2998.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2998.lits.getD i 0)) 0 1 1 h0 kb_2998_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K2998.lits KW_2998) 0 2 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2998.lits KW_2998) 0 1 = true := kg_2998_0
    have h1 : IPChk.allR (Pts.glueIB K2998.lits KW_2998) 0 2 = true := IPChk.allR_join (Pts.glueIB K2998.lits KW_2998) 0 1 1 h0 kg_2998_1
    exact h1
  have hlen : K2998.lits.length = 2 := by decide
  intro k h1 h2
  obtain rfl : k = 2998 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2998) K2998.lits KW_2998
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_528 : ∀ k, 2999 ≤ k → k < 3022 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2999 JW_2999 2999 23 jr_2999

theorem grp6_17 : ∀ k, 2966 ≤ k → k < 3022 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_514
  have a1 := Pts.fa_join a0 jr6_515
  have a2 := Pts.fa_join a1 jr6_516
  have a3 := Pts.fa_join a2 jr6_517
  have a4 := Pts.fa_join a3 jr6_518
  have a5 := Pts.fa_join a4 jr6_519
  have a6 := Pts.fa_join a5 jr6_520
  have a7 := Pts.fa_join a6 jr6_521
  have a8 := Pts.fa_join a7 jr6_522
  have a9 := Pts.fa_join a8 jr6_523
  have a10 := Pts.fa_join a9 jr6_524
  have a11 := Pts.fa_join a10 jr6_525
  have a12 := Pts.fa_join a11 jr6_526
  have a13 := Pts.fa_join a12 jr6_527
  have a14 := Pts.fa_join a13 jr6_528
  exact a14

end B334.E1x.Pts.S707
