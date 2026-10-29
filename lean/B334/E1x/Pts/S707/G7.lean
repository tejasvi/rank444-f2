import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J986
import B334.E1x.Pts.S707.J990
import B334.E1x.Pts.S707.J992
import B334.E1x.Pts.S707.J996
import B334.E1x.Pts.S707.J998
import B334.E1x.Pts.S707.J1033
import B334.E1x.Pts.S707.J1037
import B334.E1x.Pts.S707.J1039
import B334.E1x.Pts.S707.J1045
import B334.E1x.Pts.S707.J1081
import B334.E1x.Pts.S707.J1083
import B334.E1x.Pts.S707.J1122
import B334.E1x.Pts.S707.J1124
import B334.E1x.Pts.S707.J1176
import B334.E1x.Pts.S707.J1180
import B334.E1x.Pts.S707.J1182
import B334.E1x.Pts.S707.J1188
import B334.E1x.Pts.S707.J1213
import B334.E1x.Pts.S707.K985L
import B334.E1x.Pts.S707.K988L
import B334.E1x.Pts.S707.K989L
import B334.E1x.Pts.S707.K991L
import B334.E1x.Pts.S707.K994L
import B334.E1x.Pts.S707.K995L
import B334.E1x.Pts.S707.K997L
import B334.E1x.Pts.S707.K1032L
import B334.E1x.Pts.S707.K1035L
import B334.E1x.Pts.S707.K1036L
import B334.E1x.Pts.S707.K1038L
import B334.E1x.Pts.S707.K1044L
import B334.E1x.Pts.S707.K1079L
import B334.E1x.Pts.S707.K1080L
import B334.E1x.Pts.S707.K1082L
import B334.E1x.Pts.S707.K1121L
import B334.E1x.Pts.S707.K1123L
import B334.E1x.Pts.S707.K1175L
import B334.E1x.Pts.S707.K1179L
import B334.E1x.Pts.S707.K1181L
import B334.E1x.Pts.S707.K1187L
import B334.E1x.Pts.S707.K1211L
import B334.E1x.Pts.S707.K1212L
import B334.E1x.Pts.S707.K985Q0
import B334.E1x.Pts.S707.K985Q1
import B334.E1x.Pts.S707.K985Q2
import B334.E1x.Pts.S707.K985Q3
import B334.E1x.Pts.S707.K985Q4
import B334.E1x.Pts.S707.K985Q5
import B334.E1x.Pts.S707.K988Q0
import B334.E1x.Pts.S707.K988Q1
import B334.E1x.Pts.S707.K988Q2
import B334.E1x.Pts.S707.K988Q3
import B334.E1x.Pts.S707.K989Q0
import B334.E1x.Pts.S707.K989Q1
import B334.E1x.Pts.S707.K989Q2
import B334.E1x.Pts.S707.K991Q0
import B334.E1x.Pts.S707.K991Q1
import B334.E1x.Pts.S707.K991Q2
import B334.E1x.Pts.S707.K994Q0
import B334.E1x.Pts.S707.K995Q0
import B334.E1x.Pts.S707.K995Q1
import B334.E1x.Pts.S707.K997Q0
import B334.E1x.Pts.S707.K997Q1
import B334.E1x.Pts.S707.K1032Q0
import B334.E1x.Pts.S707.K1032Q1
import B334.E1x.Pts.S707.K1032Q2
import B334.E1x.Pts.S707.K1032Q3
import B334.E1x.Pts.S707.K1035Q0
import B334.E1x.Pts.S707.K1035Q1
import B334.E1x.Pts.S707.K1035Q2
import B334.E1x.Pts.S707.K1036Q0
import B334.E1x.Pts.S707.K1038Q0
import B334.E1x.Pts.S707.K1044Q0
import B334.E1x.Pts.S707.K1079Q0
import B334.E1x.Pts.S707.K1080Q0
import B334.E1x.Pts.S707.K1082Q0
import B334.E1x.Pts.S707.K1121Q0
import B334.E1x.Pts.S707.K1123Q0
import B334.E1x.Pts.S707.K1175Q0
import B334.E1x.Pts.S707.K1179Q0
import B334.E1x.Pts.S707.K1179Q1
import B334.E1x.Pts.S707.K1179Q2
import B334.E1x.Pts.S707.K1179Q3
import B334.E1x.Pts.S707.K1179Q4
import B334.E1x.Pts.S707.K1179Q5
import B334.E1x.Pts.S707.K1179Q6
import B334.E1x.Pts.S707.K1179Q7
import B334.E1x.Pts.S707.K1181Q0
import B334.E1x.Pts.S707.K1187Q0
import B334.E1x.Pts.S707.K1211Q0
import B334.E1x.Pts.S707.K1212Q0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 985 … 1214 (stage707_v6): the v5 Fin's job blocks r200 … r245 as
theorems, joined into `grp6_7` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_200 : ∀ k, 985 ≤ k → k < 986 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 686 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 1 = true := kb_985_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 1 2 h0 kb_985_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 3 5 h1 kb_985_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 8 1 h2 kb_985_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 9 13 h3 kb_985_9
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 22 6 h4 kb_985_22
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 28 3 h5 kb_985_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 31 6 h6 kb_985_31
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 37 1 h7 kb_985_37
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 38 6 h8 kb_985_38
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 44 1 h9 kb_985_44
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 45 3 h10 kb_985_45
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 48 43 h11 kb_985_48
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 91 88 h12 kb_985_91
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 179 1 h13 kb_985_179
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 180 1 h14 kb_985_180
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 181 2 h15 kb_985_181
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 183 40 h16 kb_985_183
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 223 3 h17 kb_985_223
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 226 2 h18 kb_985_226
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 228 17 h19 kb_985_228
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 245 14 h20 kb_985_245
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 259 114 h21 kb_985_259
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 373 15 h22 kb_985_373
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 388 18 h23 kb_985_388
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 406 6 h24 kb_985_406
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 412 2 h25 kb_985_412
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 459 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 414 45 h26 kb_985_414
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 459 52 h27 kb_985_459
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 511 12 h28 kb_985_511
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 523 1 h29 kb_985_523
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 524 10 h30 kb_985_524
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 534 3 h31 kb_985_534
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 537 1 h32 kb_985_537
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 545 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 538 7 h33 kb_985_538
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 545 1 h34 kb_985_545
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 546 8 h35 kb_985_546
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 554 6 h36 kb_985_554
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 560 5 h37 kb_985_560
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 565 1 h38 kb_985_565
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 566 6 h39 kb_985_566
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 572 1 h40 kb_985_572
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 573 3 h41 kb_985_573
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 577 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 576 1 h42 kb_985_576
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 577 3 h43 kb_985_577
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 581 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 580 1 h44 kb_985_580
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 581 5 h45 kb_985_581
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 587 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 586 1 h46 kb_985_586
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 587 10 h47 kb_985_587
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 597 12 h48 kb_985_597
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 609 30 h49 kb_985_609
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 639 1 h50 kb_985_639
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 640 2 h51 kb_985_640
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 642 1 h52 kb_985_642
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 643 1 h53 kb_985_643
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 644 13 h54 kb_985_644
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 657 7 h55 kb_985_657
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 664 12 h56 kb_985_664
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K985.lits.getD i 0)) 0 676 10 h57 kb_985_676
    exact h58
  have hg : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 686 = true := by
    have h0 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 1 = true := kg_985_0
    have h1 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 3 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 1 2 h0 kg_985_1
    have h2 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 8 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 3 5 h1 kg_985_3
    have h3 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 9 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 8 1 h2 kg_985_8
    have h4 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 22 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 9 13 h3 kg_985_9
    have h5 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 28 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 22 6 h4 kg_985_22
    have h6 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 31 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 28 3 h5 kg_985_28
    have h7 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 37 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 31 6 h6 kg_985_31
    have h8 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 38 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 37 1 h7 kg_985_37
    have h9 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 44 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 38 6 h8 kg_985_38
    have h10 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 45 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 44 1 h9 kg_985_44
    have h11 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 48 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 45 3 h10 kg_985_45
    have h12 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 91 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 48 43 h11 kg_985_48
    have h13 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 179 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 91 88 h12 kg_985_91
    have h14 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 180 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 179 1 h13 kg_985_179
    have h15 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 181 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 180 1 h14 kg_985_180
    have h16 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 183 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 181 2 h15 kg_985_181
    have h17 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 223 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 183 40 h16 kg_985_183
    have h18 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 226 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 223 3 h17 kg_985_223
    have h19 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 228 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 226 2 h18 kg_985_226
    have h20 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 245 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 228 17 h19 kg_985_228
    have h21 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 259 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 245 14 h20 kg_985_245
    have h22 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 373 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 259 114 h21 kg_985_259
    have h23 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 388 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 373 15 h22 kg_985_373
    have h24 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 406 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 388 18 h23 kg_985_388
    have h25 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 412 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 406 6 h24 kg_985_406
    have h26 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 414 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 412 2 h25 kg_985_412
    have h27 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 459 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 414 45 h26 kg_985_414
    have h28 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 511 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 459 52 h27 kg_985_459
    have h29 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 523 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 511 12 h28 kg_985_511
    have h30 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 524 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 523 1 h29 kg_985_523
    have h31 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 534 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 524 10 h30 kg_985_524
    have h32 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 537 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 534 3 h31 kg_985_534
    have h33 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 538 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 537 1 h32 kg_985_537
    have h34 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 545 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 538 7 h33 kg_985_538
    have h35 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 546 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 545 1 h34 kg_985_545
    have h36 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 554 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 546 8 h35 kg_985_546
    have h37 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 560 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 554 6 h36 kg_985_554
    have h38 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 565 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 560 5 h37 kg_985_560
    have h39 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 566 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 565 1 h38 kg_985_565
    have h40 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 572 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 566 6 h39 kg_985_566
    have h41 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 573 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 572 1 h40 kg_985_572
    have h42 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 576 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 573 3 h41 kg_985_573
    have h43 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 577 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 576 1 h42 kg_985_576
    have h44 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 580 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 577 3 h43 kg_985_577
    have h45 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 581 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 580 1 h44 kg_985_580
    have h46 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 586 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 581 5 h45 kg_985_581
    have h47 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 587 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 586 1 h46 kg_985_586
    have h48 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 597 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 587 10 h47 kg_985_587
    have h49 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 609 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 597 12 h48 kg_985_597
    have h50 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 639 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 609 30 h49 kg_985_609
    have h51 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 640 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 639 1 h50 kg_985_639
    have h52 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 642 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 640 2 h51 kg_985_640
    have h53 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 643 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 642 1 h52 kg_985_642
    have h54 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 644 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 643 1 h53 kg_985_643
    have h55 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 657 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 644 13 h54 kg_985_644
    have h56 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 664 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 657 7 h55 kg_985_657
    have h57 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 676 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 664 12 h56 kg_985_664
    have h58 : IPChk.allR (Pts.glueIB K985.lits KW_985) 0 686 = true := IPChk.allR_join (Pts.glueIB K985.lits KW_985) 0 676 10 h57 kg_985_676
    exact h58
  have hlen : K985.lits.length = 686 := by decide
  intro k h1 h2
  obtain rfl : k = 985 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 985) K985.lits KW_985
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_201 : ∀ k, 986 ≤ k → k < 988 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_986 JW_986 986 2 jr_986
theorem jr6_202 : ∀ k, 988 ≤ k → k < 989 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 486 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 4 = true := kb_988_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 4 3 h0 kb_988_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 7 1 h1 kb_988_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 8 14 h2 kb_988_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 22 7 h3 kb_988_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 29 3 h4 kb_988_29
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 32 2 h5 kb_988_32
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 34 1 h6 kb_988_34
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 35 12 h7 kb_988_35
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 47 101 h8 kb_988_47
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 148 7 h9 kb_988_148
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 155 37 h10 kb_988_155
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 192 2 h11 kb_988_192
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 194 30 h12 kb_988_194
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 224 1 h13 kb_988_224
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 225 33 h14 kb_988_225
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 258 15 h15 kb_988_258
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 273 119 h16 kb_988_273
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 392 19 h17 kb_988_392
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 411 14 h18 kb_988_411
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 425 2 h19 kb_988_425
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 427 5 h20 kb_988_427
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 432 6 h21 kb_988_432
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 438 4 h22 kb_988_438
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 442 1 h23 kb_988_442
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 443 12 h24 kb_988_443
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 471 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 455 16 h25 kb_988_455
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 471 2 h26 kb_988_471
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 477 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 473 4 h27 kb_988_473
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 0 477 9 h28 kb_988_477
    exact h29
  have hg : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 486 = true := by
    have h0 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 4 = true := kg_988_0
    have h1 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 7 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 4 3 h0 kg_988_4
    have h2 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 8 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 7 1 h1 kg_988_7
    have h3 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 22 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 8 14 h2 kg_988_8
    have h4 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 29 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 22 7 h3 kg_988_22
    have h5 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 32 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 29 3 h4 kg_988_29
    have h6 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 34 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 32 2 h5 kg_988_32
    have h7 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 35 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 34 1 h6 kg_988_34
    have h8 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 47 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 35 12 h7 kg_988_35
    have h9 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 148 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 47 101 h8 kg_988_47
    have h10 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 155 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 148 7 h9 kg_988_148
    have h11 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 192 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 155 37 h10 kg_988_155
    have h12 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 194 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 192 2 h11 kg_988_192
    have h13 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 224 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 194 30 h12 kg_988_194
    have h14 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 225 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 224 1 h13 kg_988_224
    have h15 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 258 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 225 33 h14 kg_988_225
    have h16 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 273 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 258 15 h15 kg_988_258
    have h17 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 392 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 273 119 h16 kg_988_273
    have h18 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 411 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 392 19 h17 kg_988_392
    have h19 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 425 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 411 14 h18 kg_988_411
    have h20 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 427 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 425 2 h19 kg_988_425
    have h21 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 432 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 427 5 h20 kg_988_427
    have h22 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 438 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 432 6 h21 kg_988_432
    have h23 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 442 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 438 4 h22 kg_988_438
    have h24 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 443 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 442 1 h23 kg_988_442
    have h25 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 455 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 443 12 h24 kg_988_443
    have h26 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 471 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 455 16 h25 kg_988_455
    have h27 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 473 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 471 2 h26 kg_988_471
    have h28 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 477 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 473 4 h27 kg_988_473
    have h29 : IPChk.allR (Pts.glueIB K988.lits KW_988) 0 486 = true := IPChk.allR_join (Pts.glueIB K988.lits KW_988) 0 477 9 h28 kg_988_477
    exact h29
  have hlen : K988.lits.length = 486 := by decide
  intro k h1 h2
  obtain rfl : k = 988 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 988) K988.lits KW_988
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_203 : ∀ k, 989 ≤ k → k < 990 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 395 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 1 = true := kb_989_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 1 2 h0 kb_989_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 3 1 h1 kb_989_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 4 1 h2 kb_989_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 5 14 h3 kb_989_5
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 19 1 h4 kb_989_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 20 3 h5 kb_989_20
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 23 2 h6 kb_989_23
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 25 24 h7 kb_989_25
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 49 114 h8 kb_989_49
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 163 2 h9 kb_989_163
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 165 29 h10 kb_989_165
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 194 2 h11 kb_989_194
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 196 6 h12 kb_989_196
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 202 2 h13 kb_989_202
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 204 52 h14 kb_989_204
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 256 54 h15 kb_989_256
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 310 2 h16 kb_989_310
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 312 14 h17 kb_989_312
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 326 1 h18 kb_989_326
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 327 12 h19 kb_989_327
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 339 2 h20 kb_989_339
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 341 1 h21 kb_989_341
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 342 2 h22 kb_989_342
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 344 1 h23 kb_989_344
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 345 3 h24 kb_989_345
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 348 3 h25 kb_989_348
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 351 19 h26 kb_989_351
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 370 18 h27 kb_989_370
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 0 388 7 h28 kb_989_388
    exact h29
  have hg : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 395 = true := by
    have h0 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 1 = true := kg_989_0
    have h1 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 3 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 1 2 h0 kg_989_1
    have h2 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 4 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 3 1 h1 kg_989_3
    have h3 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 5 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 4 1 h2 kg_989_4
    have h4 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 19 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 5 14 h3 kg_989_5
    have h5 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 20 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 19 1 h4 kg_989_19
    have h6 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 23 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 20 3 h5 kg_989_20
    have h7 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 25 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 23 2 h6 kg_989_23
    have h8 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 49 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 25 24 h7 kg_989_25
    have h9 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 163 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 49 114 h8 kg_989_49
    have h10 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 165 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 163 2 h9 kg_989_163
    have h11 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 194 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 165 29 h10 kg_989_165
    have h12 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 196 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 194 2 h11 kg_989_194
    have h13 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 202 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 196 6 h12 kg_989_196
    have h14 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 204 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 202 2 h13 kg_989_202
    have h15 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 256 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 204 52 h14 kg_989_204
    have h16 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 310 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 256 54 h15 kg_989_256
    have h17 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 312 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 310 2 h16 kg_989_310
    have h18 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 326 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 312 14 h17 kg_989_312
    have h19 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 327 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 326 1 h18 kg_989_326
    have h20 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 339 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 327 12 h19 kg_989_327
    have h21 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 341 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 339 2 h20 kg_989_339
    have h22 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 342 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 341 1 h21 kg_989_341
    have h23 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 344 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 342 2 h22 kg_989_342
    have h24 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 345 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 344 1 h23 kg_989_344
    have h25 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 348 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 345 3 h24 kg_989_345
    have h26 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 351 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 348 3 h25 kg_989_348
    have h27 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 370 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 351 19 h26 kg_989_351
    have h28 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 388 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 370 18 h27 kg_989_370
    have h29 : IPChk.allR (Pts.glueIB K989.lits KW_989) 0 395 = true := IPChk.allR_join (Pts.glueIB K989.lits KW_989) 0 388 7 h28 kg_989_388
    exact h29
  have hlen : K989.lits.length = 395 := by decide
  intro k h1 h2
  obtain rfl : k = 989 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 989) K989.lits KW_989
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_204 : ∀ k, 990 ≤ k → k < 991 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_990 JW_990 990 1 jr_990
theorem jr6_205 : ∀ k, 991 ≤ k → k < 992 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 402 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 2 = true := kb_991_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 2 2 h0 kb_991_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 4 1 h1 kb_991_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 5 13 h2 kb_991_5
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 18 1 h3 kb_991_18
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 19 4 h4 kb_991_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 23 2 h5 kb_991_23
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 25 21 h6 kb_991_25
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 46 111 h7 kb_991_46
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 157 4 h8 kb_991_157
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 161 30 h9 kb_991_161
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 191 6 h10 kb_991_191
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 197 2 h11 kb_991_197
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 199 56 h12 kb_991_199
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 255 45 h13 kb_991_255
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 300 1 h14 kb_991_300
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 301 7 h15 kb_991_301
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 308 2 h16 kb_991_308
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 310 12 h17 kb_991_310
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 322 1 h18 kb_991_322
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 323 12 h19 kb_991_323
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 336 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 335 1 h20 kb_991_335
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 336 2 h21 kb_991_336
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 338 1 h22 kb_991_338
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 339 3 h23 kb_991_339
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 342 2 h24 kb_991_342
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 344 4 h25 kb_991_344
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 348 7 h26 kb_991_348
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 355 19 h27 kb_991_355
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 391 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 374 17 h28 kb_991_374
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K991.lits.getD i 0)) 0 391 11 h29 kb_991_391
    exact h30
  have hg : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 402 = true := by
    have h0 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 2 = true := kg_991_0
    have h1 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 4 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 2 2 h0 kg_991_2
    have h2 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 5 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 4 1 h1 kg_991_4
    have h3 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 18 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 5 13 h2 kg_991_5
    have h4 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 19 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 18 1 h3 kg_991_18
    have h5 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 23 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 19 4 h4 kg_991_19
    have h6 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 25 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 23 2 h5 kg_991_23
    have h7 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 46 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 25 21 h6 kg_991_25
    have h8 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 157 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 46 111 h7 kg_991_46
    have h9 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 161 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 157 4 h8 kg_991_157
    have h10 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 191 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 161 30 h9 kg_991_161
    have h11 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 197 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 191 6 h10 kg_991_191
    have h12 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 199 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 197 2 h11 kg_991_197
    have h13 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 255 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 199 56 h12 kg_991_199
    have h14 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 300 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 255 45 h13 kg_991_255
    have h15 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 301 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 300 1 h14 kg_991_300
    have h16 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 308 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 301 7 h15 kg_991_301
    have h17 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 310 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 308 2 h16 kg_991_308
    have h18 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 322 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 310 12 h17 kg_991_310
    have h19 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 323 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 322 1 h18 kg_991_322
    have h20 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 335 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 323 12 h19 kg_991_323
    have h21 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 336 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 335 1 h20 kg_991_335
    have h22 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 338 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 336 2 h21 kg_991_336
    have h23 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 339 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 338 1 h22 kg_991_338
    have h24 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 342 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 339 3 h23 kg_991_339
    have h25 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 344 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 342 2 h24 kg_991_342
    have h26 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 348 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 344 4 h25 kg_991_344
    have h27 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 355 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 348 7 h26 kg_991_348
    have h28 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 374 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 355 19 h27 kg_991_355
    have h29 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 391 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 374 17 h28 kg_991_374
    have h30 : IPChk.allR (Pts.glueIB K991.lits KW_991) 0 402 = true := IPChk.allR_join (Pts.glueIB K991.lits KW_991) 0 391 11 h29 kg_991_391
    exact h30
  have hlen : K991.lits.length = 402 := by decide
  intro k h1 h2
  obtain rfl : k = 991 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 991) K991.lits KW_991
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_206 : ∀ k, 992 ≤ k → k < 994 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_992 JW_992 992 2 jr_992
theorem jr6_207 : ∀ k, 994 ≤ k → k < 995 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 209 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 1 = true := kb_994_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 1 1 h0 kb_994_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 2 18 h1 kb_994_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 20 46 h2 kb_994_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 66 103 h3 kb_994_66
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 169 3 h4 kb_994_169
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 172 16 h5 kb_994_172
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 188 21 h6 kb_994_188
    exact h7
  have hg : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 209 = true := by
    have h0 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 1 = true := kg_994_0
    have h1 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 2 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 1 1 h0 kg_994_1
    have h2 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 20 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 2 18 h1 kg_994_2
    have h3 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 66 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 20 46 h2 kg_994_20
    have h4 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 169 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 66 103 h3 kg_994_66
    have h5 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 172 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 169 3 h4 kg_994_169
    have h6 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 188 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 172 16 h5 kg_994_172
    have h7 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 209 = true := IPChk.allR_join (Pts.glueIB K994.lits KW_994) 0 188 21 h6 kg_994_188
    exact h7
  have hlen : K994.lits.length = 209 := by decide
  intro k h1 h2
  obtain rfl : k = 994 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 994) K994.lits KW_994
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_208 : ∀ k, 995 ≤ k → k < 996 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 220 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 1 = true := kb_995_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 1 1 h0 kb_995_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 2 13 h1 kb_995_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 15 42 h2 kb_995_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 57 101 h3 kb_995_57
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 158 1 h4 kb_995_158
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 159 11 h5 kb_995_159
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 170 1 h6 kb_995_170
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 171 9 h7 kb_995_171
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 180 2 h8 kb_995_180
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 182 7 h9 kb_995_182
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K995.lits.getD i 0)) 0 189 31 h10 kb_995_189
    exact h11
  have hg : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 220 = true := by
    have h0 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 1 = true := kg_995_0
    have h1 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 2 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 1 1 h0 kg_995_1
    have h2 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 15 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 2 13 h1 kg_995_2
    have h3 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 57 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 15 42 h2 kg_995_15
    have h4 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 158 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 57 101 h3 kg_995_57
    have h5 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 159 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 158 1 h4 kg_995_158
    have h6 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 170 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 159 11 h5 kg_995_159
    have h7 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 171 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 170 1 h6 kg_995_170
    have h8 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 180 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 171 9 h7 kg_995_171
    have h9 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 182 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 180 2 h8 kg_995_180
    have h10 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 189 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 182 7 h9 kg_995_182
    have h11 : IPChk.allR (Pts.glueIB K995.lits KW_995) 0 220 = true := IPChk.allR_join (Pts.glueIB K995.lits KW_995) 0 189 31 h10 kg_995_189
    exact h11
  have hlen : K995.lits.length = 220 := by decide
  intro k h1 h2
  obtain rfl : k = 995 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 995) K995.lits KW_995
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_209 : ∀ k, 996 ≤ k → k < 997 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_996 JW_996 996 1 jr_996
theorem jr6_210 : ∀ k, 997 ≤ k → k < 998 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 375 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 1 = true := kb_997_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 1 2 h0 kb_997_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 3 29 h1 kb_997_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 32 2 h2 kb_997_32
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 34 6 h3 kb_997_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 40 2 h4 kb_997_40
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 42 34 h5 kb_997_42
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 76 61 h6 kb_997_76
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 137 27 h7 kb_997_137
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 164 13 h8 kb_997_164
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 177 23 h9 kb_997_177
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 200 2 h10 kb_997_200
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 202 21 h11 kb_997_202
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 223 2 h12 kb_997_223
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 225 32 h13 kb_997_225
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 257 31 h14 kb_997_257
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 288 51 h15 kb_997_288
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K997.lits.getD i 0)) 0 339 36 h16 kb_997_339
    exact h17
  have hg : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 375 = true := by
    have h0 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 1 = true := kg_997_0
    have h1 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 3 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 1 2 h0 kg_997_1
    have h2 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 32 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 3 29 h1 kg_997_3
    have h3 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 34 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 32 2 h2 kg_997_32
    have h4 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 40 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 34 6 h3 kg_997_34
    have h5 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 42 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 40 2 h4 kg_997_40
    have h6 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 76 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 42 34 h5 kg_997_42
    have h7 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 137 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 76 61 h6 kg_997_76
    have h8 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 164 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 137 27 h7 kg_997_137
    have h9 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 177 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 164 13 h8 kg_997_164
    have h10 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 200 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 177 23 h9 kg_997_177
    have h11 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 202 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 200 2 h10 kg_997_200
    have h12 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 223 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 202 21 h11 kg_997_202
    have h13 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 225 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 223 2 h12 kg_997_223
    have h14 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 257 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 225 32 h13 kg_997_225
    have h15 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 288 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 257 31 h14 kg_997_257
    have h16 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 339 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 288 51 h15 kg_997_288
    have h17 : IPChk.allR (Pts.glueIB K997.lits KW_997) 0 375 = true := IPChk.allR_join (Pts.glueIB K997.lits KW_997) 0 339 36 h16 kg_997_339
    exact h17
  have hlen : K997.lits.length = 375 := by decide
  intro k h1 h2
  obtain rfl : k = 997 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 997) K997.lits KW_997
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_211 : ∀ k, 998 ≤ k → k < 1032 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_998 JW_998 998 34 jr_998
theorem jr6_212 : ∀ k, 1032 ≤ k → k < 1033 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 389 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 3 = true := kb_1032_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 3 5 h0 kb_1032_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 8 1 h1 kb_1032_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 9 10 h2 kb_1032_9
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 19 4 h3 kb_1032_19
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 23 4 h4 kb_1032_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 27 8 h5 kb_1032_27
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 35 5 h6 kb_1032_35
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 40 2 h7 kb_1032_40
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 42 2 h8 kb_1032_42
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 44 50 h9 kb_1032_44
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 94 80 h10 kb_1032_94
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 174 1 h11 kb_1032_174
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 175 2 h12 kb_1032_175
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 177 27 h13 kb_1032_177
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 204 16 h14 kb_1032_204
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 220 3 h15 kb_1032_220
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 223 33 h16 kb_1032_223
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 256 28 h17 kb_1032_256
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 284 35 h18 kb_1032_284
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 319 2 h19 kb_1032_319
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 321 8 h20 kb_1032_321
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 329 1 h21 kb_1032_329
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 330 7 h22 kb_1032_330
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 337 2 h23 kb_1032_337
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 339 2 h24 kb_1032_339
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 341 1 h25 kb_1032_341
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 342 1 h26 kb_1032_342
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 346 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 343 3 h27 kb_1032_343
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 347 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 346 1 h28 kb_1032_346
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 347 10 h29 kb_1032_347
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 357 12 h30 kb_1032_357
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 369 8 h31 kb_1032_369
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 377 1 h32 kb_1032_377
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 378 2 h33 kb_1032_378
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 380 1 h34 kb_1032_380
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 381 1 h35 kb_1032_381
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 382 2 h36 kb_1032_382
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 384 4 h37 kb_1032_384
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1032.lits.getD i 0)) 0 388 1 h38 kb_1032_388
    exact h39
  have hg : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 389 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 3 = true := kg_1032_0
    have h1 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 8 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 3 5 h0 kg_1032_3
    have h2 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 9 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 8 1 h1 kg_1032_8
    have h3 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 19 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 9 10 h2 kg_1032_9
    have h4 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 23 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 19 4 h3 kg_1032_19
    have h5 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 27 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 23 4 h4 kg_1032_23
    have h6 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 35 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 27 8 h5 kg_1032_27
    have h7 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 40 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 35 5 h6 kg_1032_35
    have h8 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 42 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 40 2 h7 kg_1032_40
    have h9 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 44 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 42 2 h8 kg_1032_42
    have h10 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 94 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 44 50 h9 kg_1032_44
    have h11 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 174 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 94 80 h10 kg_1032_94
    have h12 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 175 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 174 1 h11 kg_1032_174
    have h13 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 177 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 175 2 h12 kg_1032_175
    have h14 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 204 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 177 27 h13 kg_1032_177
    have h15 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 220 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 204 16 h14 kg_1032_204
    have h16 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 223 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 220 3 h15 kg_1032_220
    have h17 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 256 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 223 33 h16 kg_1032_223
    have h18 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 284 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 256 28 h17 kg_1032_256
    have h19 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 319 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 284 35 h18 kg_1032_284
    have h20 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 321 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 319 2 h19 kg_1032_319
    have h21 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 329 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 321 8 h20 kg_1032_321
    have h22 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 330 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 329 1 h21 kg_1032_329
    have h23 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 337 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 330 7 h22 kg_1032_330
    have h24 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 339 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 337 2 h23 kg_1032_337
    have h25 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 341 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 339 2 h24 kg_1032_339
    have h26 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 342 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 341 1 h25 kg_1032_341
    have h27 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 343 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 342 1 h26 kg_1032_342
    have h28 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 346 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 343 3 h27 kg_1032_343
    have h29 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 347 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 346 1 h28 kg_1032_346
    have h30 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 357 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 347 10 h29 kg_1032_347
    have h31 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 369 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 357 12 h30 kg_1032_357
    have h32 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 377 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 369 8 h31 kg_1032_369
    have h33 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 378 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 377 1 h32 kg_1032_377
    have h34 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 380 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 378 2 h33 kg_1032_378
    have h35 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 381 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 380 1 h34 kg_1032_380
    have h36 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 382 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 381 1 h35 kg_1032_381
    have h37 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 384 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 382 2 h36 kg_1032_382
    have h38 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 388 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 384 4 h37 kg_1032_384
    have h39 : IPChk.allR (Pts.glueIB K1032.lits KW_1032) 0 389 = true := IPChk.allR_join (Pts.glueIB K1032.lits KW_1032) 0 388 1 h38 kg_1032_388
    exact h39
  have hlen : K1032.lits.length = 389 := by decide
  intro k h1 h2
  obtain rfl : k = 1032 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1032) K1032.lits KW_1032
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_213 : ∀ k, 1033 ≤ k → k < 1035 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1033 JW_1033 1033 2 jr_1033
theorem jr6_214 : ∀ k, 1035 ≤ k → k < 1036 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 330 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 5 = true := kb_1035_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 5 2 h0 kb_1035_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 7 1 h1 kb_1035_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 8 9 h2 kb_1035_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 17 8 h3 kb_1035_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 25 2 h4 kb_1035_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 27 4 h5 kb_1035_27
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 31 2 h6 kb_1035_31
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 33 51 h7 kb_1035_33
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 84 74 h8 kb_1035_84
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 158 3 h9 kb_1035_158
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 161 34 h10 kb_1035_161
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 195 30 h11 kb_1035_195
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 225 29 h12 kb_1035_225
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 254 27 h13 kb_1035_254
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 281 1 h14 kb_1035_281
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 282 6 h15 kb_1035_282
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 288 1 h16 kb_1035_288
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 289 7 h17 kb_1035_289
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 296 2 h18 kb_1035_296
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 298 1 h19 kb_1035_298
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 299 3 h20 kb_1035_299
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 302 1 h21 kb_1035_302
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 303 5 h22 kb_1035_303
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 308 10 h23 kb_1035_308
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 318 9 h24 kb_1035_318
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1035.lits.getD i 0)) 0 327 3 h25 kb_1035_327
    exact h26
  have hg : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 330 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 5 = true := kg_1035_0
    have h1 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 7 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 5 2 h0 kg_1035_5
    have h2 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 8 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 7 1 h1 kg_1035_7
    have h3 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 17 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 8 9 h2 kg_1035_8
    have h4 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 25 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 17 8 h3 kg_1035_17
    have h5 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 27 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 25 2 h4 kg_1035_25
    have h6 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 31 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 27 4 h5 kg_1035_27
    have h7 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 33 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 31 2 h6 kg_1035_31
    have h8 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 84 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 33 51 h7 kg_1035_33
    have h9 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 158 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 84 74 h8 kg_1035_84
    have h10 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 161 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 158 3 h9 kg_1035_158
    have h11 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 195 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 161 34 h10 kg_1035_161
    have h12 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 225 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 195 30 h11 kg_1035_195
    have h13 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 254 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 225 29 h12 kg_1035_225
    have h14 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 281 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 254 27 h13 kg_1035_254
    have h15 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 282 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 281 1 h14 kg_1035_281
    have h16 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 288 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 282 6 h15 kg_1035_282
    have h17 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 289 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 288 1 h16 kg_1035_288
    have h18 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 296 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 289 7 h17 kg_1035_289
    have h19 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 298 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 296 2 h18 kg_1035_296
    have h20 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 299 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 298 1 h19 kg_1035_298
    have h21 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 302 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 299 3 h20 kg_1035_299
    have h22 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 303 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 302 1 h21 kg_1035_302
    have h23 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 308 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 303 5 h22 kg_1035_303
    have h24 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 318 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 308 10 h23 kg_1035_308
    have h25 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 327 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 318 9 h24 kg_1035_318
    have h26 : IPChk.allR (Pts.glueIB K1035.lits KW_1035) 0 330 = true := IPChk.allR_join (Pts.glueIB K1035.lits KW_1035) 0 327 3 h25 kg_1035_327
    exact h26
  have hlen : K1035.lits.length = 330 := by decide
  intro k h1 h2
  obtain rfl : k = 1035 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1035) K1035.lits KW_1035
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_215 : ∀ k, 1036 ≤ k → k < 1037 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 55 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 11 = true := kb_1036_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 11 1 h0 kb_1036_11
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 12 21 h1 kb_1036_12
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 33 22 h2 kb_1036_33
    exact h3
  have hg : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 55 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 11 = true := kg_1036_0
    have h1 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 12 = true := IPChk.allR_join (Pts.glueIB K1036.lits KW_1036) 0 11 1 h0 kg_1036_11
    have h2 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 33 = true := IPChk.allR_join (Pts.glueIB K1036.lits KW_1036) 0 12 21 h1 kg_1036_12
    have h3 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 55 = true := IPChk.allR_join (Pts.glueIB K1036.lits KW_1036) 0 33 22 h2 kg_1036_33
    exact h3
  have hlen : K1036.lits.length = 55 := by decide
  intro k h1 h2
  obtain rfl : k = 1036 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1036) K1036.lits KW_1036
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_216 : ∀ k, 1037 ≤ k → k < 1038 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1037 JW_1037 1037 1 jr_1037
theorem jr6_217 : ∀ k, 1038 ≤ k → k < 1039 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 84 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 11 = true := kb_1038_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 11 1 h0 kb_1038_11
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 12 21 h1 kb_1038_12
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 33 16 h2 kb_1038_33
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 49 5 h3 kb_1038_49
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 54 27 h4 kb_1038_54
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 81 3 h5 kb_1038_81
    exact h6
  have hg : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 84 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 11 = true := kg_1038_0
    have h1 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 12 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 11 1 h0 kg_1038_11
    have h2 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 33 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 12 21 h1 kg_1038_12
    have h3 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 49 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 33 16 h2 kg_1038_33
    have h4 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 54 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 49 5 h3 kg_1038_49
    have h5 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 81 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 54 27 h4 kg_1038_54
    have h6 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 84 = true := IPChk.allR_join (Pts.glueIB K1038.lits KW_1038) 0 81 3 h5 kg_1038_81
    exact h6
  have hlen : K1038.lits.length = 84 := by decide
  intro k h1 h2
  obtain rfl : k = 1038 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1038) K1038.lits KW_1038
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_218 : ∀ k, 1039 ≤ k → k < 1044 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1039 JW_1039 1039 5 jr_1039
theorem jr6_219 : ∀ k, 1044 ≤ k → k < 1045 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 159 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 1 = true := kb_1044_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 1 12 h0 kb_1044_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 13 103 h1 kb_1044_13
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 116 43 h2 kb_1044_116
    exact h3
  have hg : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 159 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 1 = true := kg_1044_0
    have h1 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 13 = true := IPChk.allR_join (Pts.glueIB K1044.lits KW_1044) 0 1 12 h0 kg_1044_1
    have h2 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 116 = true := IPChk.allR_join (Pts.glueIB K1044.lits KW_1044) 0 13 103 h1 kg_1044_13
    have h3 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 159 = true := IPChk.allR_join (Pts.glueIB K1044.lits KW_1044) 0 116 43 h2 kg_1044_116
    exact h3
  have hlen : K1044.lits.length = 159 := by decide
  intro k h1 h2
  obtain rfl : k = 1044 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1044) K1044.lits KW_1044
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_220 : ∀ k, 1045 ≤ k → k < 1077 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1045 JW_1045 1045 32 jr_1045
theorem jr6_221 : ∀ k, 1077 ≤ k → k < 1078 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1045 JW_1045 1077 1 jr_1077
theorem jr6_222 : ∀ k, 1078 ≤ k → k < 1079 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1045 JW_1045 1078 1 jr_1078
theorem jr6_223 : ∀ k, 1079 ≤ k → k < 1080 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 56 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 10 = true := kb_1079_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 10 17 h0 kb_1079_10
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 27 7 h1 kb_1079_27
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 34 7 h2 kb_1079_34
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1079.lits.getD i 0)) 0 41 15 h3 kb_1079_41
    exact h4
  have hg : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 56 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 10 = true := kg_1079_0
    have h1 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 27 = true := IPChk.allR_join (Pts.glueIB K1079.lits KW_1079) 0 10 17 h0 kg_1079_10
    have h2 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 34 = true := IPChk.allR_join (Pts.glueIB K1079.lits KW_1079) 0 27 7 h1 kg_1079_27
    have h3 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 41 = true := IPChk.allR_join (Pts.glueIB K1079.lits KW_1079) 0 34 7 h2 kg_1079_34
    have h4 : IPChk.allR (Pts.glueIB K1079.lits KW_1079) 0 56 = true := IPChk.allR_join (Pts.glueIB K1079.lits KW_1079) 0 41 15 h3 kg_1079_41
    exact h4
  have hlen : K1079.lits.length = 56 := by decide
  intro k h1 h2
  obtain rfl : k = 1079 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1079) K1079.lits KW_1079
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_224 : ∀ k, 1080 ≤ k → k < 1081 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 40 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 2 = true := kb_1080_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 2 6 h0 kb_1080_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 8 12 h1 kb_1080_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 20 5 h2 kb_1080_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 25 6 h3 kb_1080_25
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 31 9 h4 kb_1080_31
    exact h5
  have hg : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 40 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 2 = true := kg_1080_0
    have h1 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 8 = true := IPChk.allR_join (Pts.glueIB K1080.lits KW_1080) 0 2 6 h0 kg_1080_2
    have h2 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 20 = true := IPChk.allR_join (Pts.glueIB K1080.lits KW_1080) 0 8 12 h1 kg_1080_8
    have h3 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 25 = true := IPChk.allR_join (Pts.glueIB K1080.lits KW_1080) 0 20 5 h2 kg_1080_20
    have h4 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 31 = true := IPChk.allR_join (Pts.glueIB K1080.lits KW_1080) 0 25 6 h3 kg_1080_25
    have h5 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 40 = true := IPChk.allR_join (Pts.glueIB K1080.lits KW_1080) 0 31 9 h4 kg_1080_31
    exact h5
  have hlen : K1080.lits.length = 40 := by decide
  intro k h1 h2
  obtain rfl : k = 1080 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1080) K1080.lits KW_1080
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_225 : ∀ k, 1081 ≤ k → k < 1082 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1081 JW_1081 1081 1 jr_1081
theorem jr6_226 : ∀ k, 1082 ≤ k → k < 1083 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 163 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 1 = true := kb_1082_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 1 9 h0 kb_1082_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 10 101 h1 kb_1082_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1082.lits.getD i 0)) 0 111 52 h2 kb_1082_111
    exact h3
  have hg : IPChk.allR (Pts.glueIB K1082.lits KW_1082) 0 163 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1082.lits KW_1082) 0 1 = true := kg_1082_0
    have h1 : IPChk.allR (Pts.glueIB K1082.lits KW_1082) 0 10 = true := IPChk.allR_join (Pts.glueIB K1082.lits KW_1082) 0 1 9 h0 kg_1082_1
    have h2 : IPChk.allR (Pts.glueIB K1082.lits KW_1082) 0 111 = true := IPChk.allR_join (Pts.glueIB K1082.lits KW_1082) 0 10 101 h1 kg_1082_10
    have h3 : IPChk.allR (Pts.glueIB K1082.lits KW_1082) 0 163 = true := IPChk.allR_join (Pts.glueIB K1082.lits KW_1082) 0 111 52 h2 kg_1082_111
    exact h3
  have hlen : K1082.lits.length = 163 := by decide
  intro k h1 h2
  obtain rfl : k = 1082 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1082) K1082.lits KW_1082
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_227 : ∀ k, 1083 ≤ k → k < 1121 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1083 JW_1083 1083 38 jr_1083
theorem jr6_228 : ∀ k, 1121 ≤ k → k < 1122 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 45 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 9 = true := kb_1121_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 9 2 h0 kb_1121_9
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 11 14 h1 kb_1121_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 25 20 h2 kb_1121_25
    exact h3
  have hg : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 45 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 9 = true := kg_1121_0
    have h1 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 11 = true := IPChk.allR_join (Pts.glueIB K1121.lits KW_1121) 0 9 2 h0 kg_1121_9
    have h2 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 25 = true := IPChk.allR_join (Pts.glueIB K1121.lits KW_1121) 0 11 14 h1 kg_1121_11
    have h3 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 45 = true := IPChk.allR_join (Pts.glueIB K1121.lits KW_1121) 0 25 20 h2 kg_1121_25
    exact h3
  have hlen : K1121.lits.length = 45 := by decide
  intro k h1 h2
  obtain rfl : k = 1121 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1121) K1121.lits KW_1121
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_229 : ∀ k, 1122 ≤ k → k < 1123 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1122 JW_1122 1122 1 jr_1122
theorem jr6_230 : ∀ k, 1123 ≤ k → k < 1124 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 61 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 8 = true := kb_1123_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 8 7 h0 kb_1123_8
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 15 8 h1 kb_1123_15
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 23 38 h2 kb_1123_23
    exact h3
  have hg : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 61 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 8 = true := kg_1123_0
    have h1 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 15 = true := IPChk.allR_join (Pts.glueIB K1123.lits KW_1123) 0 8 7 h0 kg_1123_8
    have h2 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 23 = true := IPChk.allR_join (Pts.glueIB K1123.lits KW_1123) 0 15 8 h1 kg_1123_15
    have h3 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 61 = true := IPChk.allR_join (Pts.glueIB K1123.lits KW_1123) 0 23 38 h2 kg_1123_23
    exact h3
  have hlen : K1123.lits.length = 61 := by decide
  intro k h1 h2
  obtain rfl : k = 1123 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1123) K1123.lits KW_1123
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_231 : ∀ k, 1124 ≤ k → k < 1175 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1124 JW_1124 1124 51 jr_1124
theorem jr6_232 : ∀ k, 1175 ≤ k → k < 1176 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 6 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 1 = true := kb_1175_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 1 1 h0 kb_1175_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 2 2 h1 kb_1175_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 4 1 h2 kb_1175_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1175.lits.getD i 0)) 0 5 1 h3 kb_1175_5
    exact h4
  have hg : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 6 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 1 = true := kg_1175_0
    have h1 : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 2 = true := IPChk.allR_join (Pts.glueIB K1175.lits KW_1175) 0 1 1 h0 kg_1175_1
    have h2 : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 4 = true := IPChk.allR_join (Pts.glueIB K1175.lits KW_1175) 0 2 2 h1 kg_1175_2
    have h3 : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 5 = true := IPChk.allR_join (Pts.glueIB K1175.lits KW_1175) 0 4 1 h2 kg_1175_4
    have h4 : IPChk.allR (Pts.glueIB K1175.lits KW_1175) 0 6 = true := IPChk.allR_join (Pts.glueIB K1175.lits KW_1175) 0 5 1 h3 kg_1175_5
    exact h4
  have hlen : K1175.lits.length = 6 := by decide
  intro k h1 h2
  obtain rfl : k = 1175 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1175) K1175.lits KW_1175
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_233 : ∀ k, 1176 ≤ k → k < 1177 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1176 JW_1176 1176 1 jr_1176
theorem jr6_234 : ∀ k, 1177 ≤ k → k < 1178 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1176 JW_1176 1177 1 jr_1177
theorem jr6_235 : ∀ k, 1178 ≤ k → k < 1179 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1176 JW_1176 1178 1 jr_1178
theorem jr6_236 : ∀ k, 1179 ≤ k → k < 1180 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 854 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 5 = true := kb_1179_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 5 3 h0 kb_1179_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 8 8 h1 kb_1179_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 16 8 h2 kb_1179_16
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 24 3 h3 kb_1179_24
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 27 5 h4 kb_1179_27
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 32 4 h5 kb_1179_32
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 36 7 h6 kb_1179_36
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 43 5 h7 kb_1179_43
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 48 8 h8 kb_1179_48
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 56 11 h9 kb_1179_56
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 67 19 h10 kb_1179_67
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 86 2 h11 kb_1179_86
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 88 6 h12 kb_1179_88
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 94 2 h13 kb_1179_94
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 96 22 h14 kb_1179_96
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 118 3 h15 kb_1179_118
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 121 6 h16 kb_1179_121
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 127 5 h17 kb_1179_127
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 132 18 h18 kb_1179_132
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 150 1 h19 kb_1179_150
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 151 2 h20 kb_1179_151
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 153 1 h21 kb_1179_153
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 154 2 h22 kb_1179_154
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 156 5 h23 kb_1179_156
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 161 2 h24 kb_1179_161
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 163 1 h25 kb_1179_163
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 164 3 h26 kb_1179_164
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 167 3 h27 kb_1179_167
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 170 10 h28 kb_1179_170
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 180 6 h29 kb_1179_180
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 186 2 h30 kb_1179_186
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 188 17 h31 kb_1179_188
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 205 10 h32 kb_1179_205
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 215 20 h33 kb_1179_215
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 235 8 h34 kb_1179_235
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 243 6 h35 kb_1179_243
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 249 5 h36 kb_1179_249
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 254 22 h37 kb_1179_254
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 276 2 h38 kb_1179_276
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 278 16 h39 kb_1179_278
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 294 8 h40 kb_1179_294
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 302 53 h41 kb_1179_302
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 355 4 h42 kb_1179_355
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 359 2 h43 kb_1179_359
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 361 22 h44 kb_1179_361
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 383 2 h45 kb_1179_383
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 385 21 h46 kb_1179_385
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 406 33 h47 kb_1179_406
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 439 13 h48 kb_1179_439
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 471 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 452 19 h49 kb_1179_452
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 471 2 h50 kb_1179_471
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 473 1 h51 kb_1179_473
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 474 11 h52 kb_1179_474
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 485 2 h53 kb_1179_485
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 487 1 h54 kb_1179_487
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 488 4 h55 kb_1179_488
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 498 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 492 6 h56 kb_1179_492
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 528 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 498 30 h57 kb_1179_498
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 528 60 h58 kb_1179_528
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 588 13 h59 kb_1179_588
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 601 2 h60 kb_1179_601
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 619 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 603 16 h61 kb_1179_603
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 619 3 h62 kb_1179_619
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 622 2 h63 kb_1179_622
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 624 15 h64 kb_1179_624
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 639 23 h65 kb_1179_639
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 662 24 h66 kb_1179_662
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 686 2 h67 kb_1179_686
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 688 13 h68 kb_1179_688
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 701 32 h69 kb_1179_701
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 768 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 733 35 h70 kb_1179_733
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 790 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 768 22 h71 kb_1179_768
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 790 1 h72 kb_1179_790
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 791 7 h73 kb_1179_791
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 812 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 798 14 h74 kb_1179_798
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 832 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 812 20 h75 kb_1179_812
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 852 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 832 20 h76 kb_1179_832
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 854 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1179.lits.getD i 0)) 0 852 2 h77 kb_1179_852
    exact h78
  have hg : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 854 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 5 = true := kg_1179_0
    have h1 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 8 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 5 3 h0 kg_1179_5
    have h2 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 16 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 8 8 h1 kg_1179_8
    have h3 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 24 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 16 8 h2 kg_1179_16
    have h4 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 27 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 24 3 h3 kg_1179_24
    have h5 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 32 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 27 5 h4 kg_1179_27
    have h6 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 36 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 32 4 h5 kg_1179_32
    have h7 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 43 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 36 7 h6 kg_1179_36
    have h8 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 48 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 43 5 h7 kg_1179_43
    have h9 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 56 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 48 8 h8 kg_1179_48
    have h10 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 67 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 56 11 h9 kg_1179_56
    have h11 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 86 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 67 19 h10 kg_1179_67
    have h12 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 88 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 86 2 h11 kg_1179_86
    have h13 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 94 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 88 6 h12 kg_1179_88
    have h14 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 96 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 94 2 h13 kg_1179_94
    have h15 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 118 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 96 22 h14 kg_1179_96
    have h16 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 121 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 118 3 h15 kg_1179_118
    have h17 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 127 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 121 6 h16 kg_1179_121
    have h18 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 132 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 127 5 h17 kg_1179_127
    have h19 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 150 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 132 18 h18 kg_1179_132
    have h20 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 151 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 150 1 h19 kg_1179_150
    have h21 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 153 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 151 2 h20 kg_1179_151
    have h22 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 154 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 153 1 h21 kg_1179_153
    have h23 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 156 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 154 2 h22 kg_1179_154
    have h24 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 161 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 156 5 h23 kg_1179_156
    have h25 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 163 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 161 2 h24 kg_1179_161
    have h26 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 164 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 163 1 h25 kg_1179_163
    have h27 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 167 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 164 3 h26 kg_1179_164
    have h28 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 170 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 167 3 h27 kg_1179_167
    have h29 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 180 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 170 10 h28 kg_1179_170
    have h30 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 186 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 180 6 h29 kg_1179_180
    have h31 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 188 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 186 2 h30 kg_1179_186
    have h32 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 205 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 188 17 h31 kg_1179_188
    have h33 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 215 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 205 10 h32 kg_1179_205
    have h34 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 235 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 215 20 h33 kg_1179_215
    have h35 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 243 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 235 8 h34 kg_1179_235
    have h36 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 249 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 243 6 h35 kg_1179_243
    have h37 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 254 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 249 5 h36 kg_1179_249
    have h38 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 276 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 254 22 h37 kg_1179_254
    have h39 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 278 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 276 2 h38 kg_1179_276
    have h40 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 294 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 278 16 h39 kg_1179_278
    have h41 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 302 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 294 8 h40 kg_1179_294
    have h42 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 355 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 302 53 h41 kg_1179_302
    have h43 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 359 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 355 4 h42 kg_1179_355
    have h44 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 361 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 359 2 h43 kg_1179_359
    have h45 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 383 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 361 22 h44 kg_1179_361
    have h46 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 385 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 383 2 h45 kg_1179_383
    have h47 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 406 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 385 21 h46 kg_1179_385
    have h48 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 439 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 406 33 h47 kg_1179_406
    have h49 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 452 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 439 13 h48 kg_1179_439
    have h50 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 471 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 452 19 h49 kg_1179_452
    have h51 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 473 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 471 2 h50 kg_1179_471
    have h52 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 474 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 473 1 h51 kg_1179_473
    have h53 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 485 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 474 11 h52 kg_1179_474
    have h54 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 487 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 485 2 h53 kg_1179_485
    have h55 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 488 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 487 1 h54 kg_1179_487
    have h56 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 492 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 488 4 h55 kg_1179_488
    have h57 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 498 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 492 6 h56 kg_1179_492
    have h58 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 528 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 498 30 h57 kg_1179_498
    have h59 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 588 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 528 60 h58 kg_1179_528
    have h60 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 601 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 588 13 h59 kg_1179_588
    have h61 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 603 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 601 2 h60 kg_1179_601
    have h62 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 619 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 603 16 h61 kg_1179_603
    have h63 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 622 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 619 3 h62 kg_1179_619
    have h64 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 624 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 622 2 h63 kg_1179_622
    have h65 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 639 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 624 15 h64 kg_1179_624
    have h66 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 662 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 639 23 h65 kg_1179_639
    have h67 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 686 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 662 24 h66 kg_1179_662
    have h68 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 688 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 686 2 h67 kg_1179_686
    have h69 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 701 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 688 13 h68 kg_1179_688
    have h70 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 733 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 701 32 h69 kg_1179_701
    have h71 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 768 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 733 35 h70 kg_1179_733
    have h72 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 790 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 768 22 h71 kg_1179_768
    have h73 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 791 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 790 1 h72 kg_1179_790
    have h74 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 798 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 791 7 h73 kg_1179_791
    have h75 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 812 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 798 14 h74 kg_1179_798
    have h76 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 832 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 812 20 h75 kg_1179_812
    have h77 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 852 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 832 20 h76 kg_1179_832
    have h78 : IPChk.allR (Pts.glueIB K1179.lits KW_1179) 0 854 = true := IPChk.allR_join (Pts.glueIB K1179.lits KW_1179) 0 852 2 h77 kg_1179_852
    exact h78
  have hlen : K1179.lits.length = 854 := by decide
  intro k h1 h2
  obtain rfl : k = 1179 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1179) K1179.lits KW_1179
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_237 : ∀ k, 1180 ≤ k → k < 1181 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1180 JW_1180 1180 1 jr_1180
theorem jr6_238 : ∀ k, 1181 ≤ k → k < 1182 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 144 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 3 = true := kb_1181_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 3 12 h0 kb_1181_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 15 16 h1 kb_1181_15
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 31 46 h2 kb_1181_31
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 77 23 h3 kb_1181_77
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1181.lits.getD i 0)) 0 100 44 h4 kb_1181_100
    exact h5
  have hg : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 144 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 3 = true := kg_1181_0
    have h1 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 15 = true := IPChk.allR_join (Pts.glueIB K1181.lits KW_1181) 0 3 12 h0 kg_1181_3
    have h2 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 31 = true := IPChk.allR_join (Pts.glueIB K1181.lits KW_1181) 0 15 16 h1 kg_1181_15
    have h3 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 77 = true := IPChk.allR_join (Pts.glueIB K1181.lits KW_1181) 0 31 46 h2 kg_1181_31
    have h4 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 100 = true := IPChk.allR_join (Pts.glueIB K1181.lits KW_1181) 0 77 23 h3 kg_1181_77
    have h5 : IPChk.allR (Pts.glueIB K1181.lits KW_1181) 0 144 = true := IPChk.allR_join (Pts.glueIB K1181.lits KW_1181) 0 100 44 h4 kg_1181_100
    exact h5
  have hlen : K1181.lits.length = 144 := by decide
  intro k h1 h2
  obtain rfl : k = 1181 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1181) K1181.lits KW_1181
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_239 : ∀ k, 1182 ≤ k → k < 1187 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1182 JW_1182 1182 5 jr_1182
theorem jr6_240 : ∀ k, 1187 ≤ k → k < 1188 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 50 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 6 = true := kb_1187_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 6 2 h0 kb_1187_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 8 12 h1 kb_1187_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 20 1 h2 kb_1187_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 21 4 h3 kb_1187_21
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 25 18 h4 kb_1187_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1187.lits.getD i 0)) 0 43 7 h5 kb_1187_43
    exact h6
  have hg : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 50 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 6 = true := kg_1187_0
    have h1 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 8 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 6 2 h0 kg_1187_6
    have h2 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 20 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 8 12 h1 kg_1187_8
    have h3 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 21 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 20 1 h2 kg_1187_20
    have h4 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 25 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 21 4 h3 kg_1187_21
    have h5 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 43 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 25 18 h4 kg_1187_25
    have h6 : IPChk.allR (Pts.glueIB K1187.lits KW_1187) 0 50 = true := IPChk.allR_join (Pts.glueIB K1187.lits KW_1187) 0 43 7 h5 kg_1187_43
    exact h6
  have hlen : K1187.lits.length = 50 := by decide
  intro k h1 h2
  obtain rfl : k = 1187 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1187) K1187.lits KW_1187
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_241 : ∀ k, 1188 ≤ k → k < 1201 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1188 JW_1188 1188 13 jr_1188
theorem jr6_242 : ∀ k, 1201 ≤ k → k < 1211 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1188 JW_1188 1201 10 jr_1201
theorem jr6_243 : ∀ k, 1211 ≤ k → k < 1212 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 1 = true := kb_1211_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 1 1 h0 kb_1211_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1211.lits.getD i 0)) 0 2 1 h1 kb_1211_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K1211.lits KW_1211) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1211.lits KW_1211) 0 1 = true := kg_1211_0
    have h1 : IPChk.allR (Pts.glueIB K1211.lits KW_1211) 0 2 = true := IPChk.allR_join (Pts.glueIB K1211.lits KW_1211) 0 1 1 h0 kg_1211_1
    have h2 : IPChk.allR (Pts.glueIB K1211.lits KW_1211) 0 3 = true := IPChk.allR_join (Pts.glueIB K1211.lits KW_1211) 0 2 1 h1 kg_1211_2
    exact h2
  have hlen : K1211.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 1211 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1211) K1211.lits KW_1211
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_244 : ∀ k, 1212 ≤ k → k < 1213 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 1 = true := kb_1212_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 1 1 h0 kb_1212_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1212.lits.getD i 0)) 0 2 1 h1 kb_1212_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 0 1 = true := kg_1212_0
    have h1 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 0 2 = true := IPChk.allR_join (Pts.glueIB K1212.lits KW_1212) 0 1 1 h0 kg_1212_1
    have h2 : IPChk.allR (Pts.glueIB K1212.lits KW_1212) 0 3 = true := IPChk.allR_join (Pts.glueIB K1212.lits KW_1212) 0 2 1 h1 kg_1212_2
    exact h2
  have hlen : K1212.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 1212 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1212) K1212.lits KW_1212
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_245 : ∀ k, 1213 ≤ k → k < 1215 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1213 JW_1213 1213 2 jr_1213

theorem grp6_7 : ∀ k, 985 ≤ k → k < 1215 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_200
  have a1 := Pts.fa_join a0 jr6_201
  have a2 := Pts.fa_join a1 jr6_202
  have a3 := Pts.fa_join a2 jr6_203
  have a4 := Pts.fa_join a3 jr6_204
  have a5 := Pts.fa_join a4 jr6_205
  have a6 := Pts.fa_join a5 jr6_206
  have a7 := Pts.fa_join a6 jr6_207
  have a8 := Pts.fa_join a7 jr6_208
  have a9 := Pts.fa_join a8 jr6_209
  have a10 := Pts.fa_join a9 jr6_210
  have a11 := Pts.fa_join a10 jr6_211
  have a12 := Pts.fa_join a11 jr6_212
  have a13 := Pts.fa_join a12 jr6_213
  have a14 := Pts.fa_join a13 jr6_214
  have a15 := Pts.fa_join a14 jr6_215
  have a16 := Pts.fa_join a15 jr6_216
  have a17 := Pts.fa_join a16 jr6_217
  have a18 := Pts.fa_join a17 jr6_218
  have a19 := Pts.fa_join a18 jr6_219
  have a20 := Pts.fa_join a19 jr6_220
  have a21 := Pts.fa_join a20 jr6_221
  have a22 := Pts.fa_join a21 jr6_222
  have a23 := Pts.fa_join a22 jr6_223
  have a24 := Pts.fa_join a23 jr6_224
  have a25 := Pts.fa_join a24 jr6_225
  have a26 := Pts.fa_join a25 jr6_226
  have a27 := Pts.fa_join a26 jr6_227
  have a28 := Pts.fa_join a27 jr6_228
  have a29 := Pts.fa_join a28 jr6_229
  have a30 := Pts.fa_join a29 jr6_230
  have a31 := Pts.fa_join a30 jr6_231
  have a32 := Pts.fa_join a31 jr6_232
  have a33 := Pts.fa_join a32 jr6_233
  have a34 := Pts.fa_join a33 jr6_234
  have a35 := Pts.fa_join a34 jr6_235
  have a36 := Pts.fa_join a35 jr6_236
  have a37 := Pts.fa_join a36 jr6_237
  have a38 := Pts.fa_join a37 jr6_238
  have a39 := Pts.fa_join a38 jr6_239
  have a40 := Pts.fa_join a39 jr6_240
  have a41 := Pts.fa_join a40 jr6_241
  have a42 := Pts.fa_join a41 jr6_242
  have a43 := Pts.fa_join a42 jr6_243
  have a44 := Pts.fa_join a43 jr6_244
  have a45 := Pts.fa_join a44 jr6_245
  exact a45

end B334.E1x.Pts.S707
