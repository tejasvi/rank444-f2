import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J2457
import B334.E1x.Pts.S707.J2459
import B334.E1x.Pts.S707.J2461
import B334.E1x.Pts.S707.J2465
import B334.E1x.Pts.S707.J2467
import B334.E1x.Pts.S707.J2471
import B334.E1x.Pts.S707.J2473
import B334.E1x.Pts.S707.J2481
import B334.E1x.Pts.S707.J2504
import B334.E1x.Pts.S707.J2560
import B334.E1x.Pts.S707.J2562
import B334.E1x.Pts.S707.K2456L
import B334.E1x.Pts.S707.K2458L
import B334.E1x.Pts.S707.K2460L
import B334.E1x.Pts.S707.K2463L
import B334.E1x.Pts.S707.K2464L
import B334.E1x.Pts.S707.K2466L
import B334.E1x.Pts.S707.K2469L
import B334.E1x.Pts.S707.K2470L
import B334.E1x.Pts.S707.K2472L
import B334.E1x.Pts.S707.K2480L
import B334.E1x.Pts.S707.K2503L
import B334.E1x.Pts.S707.K2559L
import B334.E1x.Pts.S707.K2561L
import B334.E1x.Pts.S707.K2456Q0
import B334.E1x.Pts.S707.K2456Q1
import B334.E1x.Pts.S707.K2456Q2
import B334.E1x.Pts.S707.K2456Q3
import B334.E1x.Pts.S707.K2456Q4
import B334.E1x.Pts.S707.K2456Q5
import B334.E1x.Pts.S707.K2456Q6
import B334.E1x.Pts.S707.K2456Q7
import B334.E1x.Pts.S707.K2456Q8
import B334.E1x.Pts.S707.K2456Q9
import B334.E1x.Pts.S707.K2458Q0
import B334.E1x.Pts.S707.K2458Q1
import B334.E1x.Pts.S707.K2458Q2
import B334.E1x.Pts.S707.K2458Q3
import B334.E1x.Pts.S707.K2458Q4
import B334.E1x.Pts.S707.K2458Q5
import B334.E1x.Pts.S707.K2458Q6
import B334.E1x.Pts.S707.K2458Q7
import B334.E1x.Pts.S707.K2458Q8
import B334.E1x.Pts.S707.K2458Q9
import B334.E1x.Pts.S707.K2460Q0
import B334.E1x.Pts.S707.K2460Q1
import B334.E1x.Pts.S707.K2460Q2
import B334.E1x.Pts.S707.K2460Q3
import B334.E1x.Pts.S707.K2460Q4
import B334.E1x.Pts.S707.K2460Q5
import B334.E1x.Pts.S707.K2460Q6
import B334.E1x.Pts.S707.K2460Q7
import B334.E1x.Pts.S707.K2460Q8
import B334.E1x.Pts.S707.K2460Q9
import B334.E1x.Pts.S707.K2463Q0
import B334.E1x.Pts.S707.K2463Q1
import B334.E1x.Pts.S707.K2464Q0
import B334.E1x.Pts.S707.K2464Q1
import B334.E1x.Pts.S707.K2464Q2
import B334.E1x.Pts.S707.K2466Q0
import B334.E1x.Pts.S707.K2466Q1
import B334.E1x.Pts.S707.K2466Q2
import B334.E1x.Pts.S707.K2466Q3
import B334.E1x.Pts.S707.K2469Q0
import B334.E1x.Pts.S707.K2469Q1
import B334.E1x.Pts.S707.K2470Q0
import B334.E1x.Pts.S707.K2470Q1
import B334.E1x.Pts.S707.K2470Q2
import B334.E1x.Pts.S707.K2472Q0
import B334.E1x.Pts.S707.K2480Q0
import B334.E1x.Pts.S707.K2503Q0
import B334.E1x.Pts.S707.K2559Q0
import B334.E1x.Pts.S707.K2559Q1
import B334.E1x.Pts.S707.K2561Q0
import B334.E1x.Pts.S707.K2456Q10
import B334.E1x.Pts.S707.K2456Q11
import B334.E1x.Pts.S707.K2456Q12
import B334.E1x.Pts.S707.K2458Q10
import B334.E1x.Pts.S707.K2460Q10
import B334.E1x.Pts.S707.K2460Q11
import B334.E1x.Pts.S707.K2460Q12
import B334.E1x.Pts.S707.K2460Q13
import B334.E1x.Pts.S707.K2460Q14

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 2456 … 2563 (stage707_v6): the v5 Fin's job blocks r428 … r454 as
theorems, joined into `grp6_15` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_428 : ∀ k, 2456 ≤ k → k < 2457 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1695 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 5 = true := kb_2456_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 5 1 h0 kb_2456_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 6 2 h1 kb_2456_6
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 8 4 h2 kb_2456_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 12 2 h3 kb_2456_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 14 5 h4 kb_2456_14
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 19 9 h5 kb_2456_19
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 28 2 h6 kb_2456_28
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 30 2 h7 kb_2456_30
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 32 1 h8 kb_2456_32
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 33 2 h9 kb_2456_33
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 35 10 h10 kb_2456_35
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 45 2 h11 kb_2456_45
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 47 1 h12 kb_2456_47
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 48 11 h13 kb_2456_48
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 59 2 h14 kb_2456_59
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 61 1 h15 kb_2456_61
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 62 8 h16 kb_2456_62
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 70 2 h17 kb_2456_70
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 72 1 h18 kb_2456_72
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 73 8 h19 kb_2456_73
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 81 1 h20 kb_2456_81
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 82 11 h21 kb_2456_82
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 93 29 h22 kb_2456_93
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 122 2 h23 kb_2456_122
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 124 6 h24 kb_2456_124
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 130 2 h25 kb_2456_130
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 132 40 h26 kb_2456_132
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 172 27 h27 kb_2456_172
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 199 4 h28 kb_2456_199
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 203 16 h29 kb_2456_203
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 219 2 h30 kb_2456_219
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 221 1 h31 kb_2456_221
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 222 1 h32 kb_2456_222
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 223 6 h33 kb_2456_223
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 229 2 h34 kb_2456_229
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 231 2 h35 kb_2456_231
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 233 4 h36 kb_2456_233
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 237 2 h37 kb_2456_237
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 239 5 h38 kb_2456_239
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 244 45 h39 kb_2456_244
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 289 78 h40 kb_2456_289
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 367 3 h41 kb_2456_367
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 370 7 h42 kb_2456_370
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 377 25 h43 kb_2456_377
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 402 6 h44 kb_2456_402
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 408 2 h45 kb_2456_408
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 410 50 h46 kb_2456_410
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 460 40 h47 kb_2456_460
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 501 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 500 1 h48 kb_2456_500
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 501 1 h49 kb_2456_501
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 502 5 h50 kb_2456_502
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 507 12 h51 kb_2456_507
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 519 20 h52 kb_2456_519
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 545 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 539 6 h53 kb_2456_539
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 545 4 h54 kb_2456_545
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 549 77 h55 kb_2456_549
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 626 3 h56 kb_2456_626
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 637 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 629 8 h57 kb_2456_629
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 637 2 h58 kb_2456_637
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 639 1 h59 kb_2456_639
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 640 6 h60 kb_2456_640
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 646 46 h61 kb_2456_646
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 766 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 692 74 h62 kb_2456_692
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 766 4 h63 kb_2456_766
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 798 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 770 28 h64 kb_2456_770
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 798 6 h65 kb_2456_798
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 806 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 804 2 h66 kb_2456_804
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 856 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 806 50 h67 kb_2456_806
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 895 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 856 39 h68 kb_2456_856
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 900 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 895 5 h69 kb_2456_895
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 900 20 h70 kb_2456_900
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 920 2 h71 kb_2456_920
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 940 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 922 18 h72 kb_2456_922
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 942 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 940 2 h73 kb_2456_940
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 942 32 h74 kb_2456_942
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1002 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 974 28 h75 kb_2456_974
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1004 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1002 2 h76 kb_2456_1002
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1015 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1004 11 h77 kb_2456_1004
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1036 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1015 21 h78 kb_2456_1015
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1084 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1036 48 h79 kb_2456_1036
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1084 34 h80 kb_2456_1084
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1118 2 h81 kb_2456_1118
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1120 4 h82 kb_2456_1120
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1124 1 h83 kb_2456_1124
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1125 1 h84 kb_2456_1125
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1126 1 h85 kb_2456_1126
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1127 1 h86 kb_2456_1127
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1128 4 h87 kb_2456_1128
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1132 16 h88 kb_2456_1132
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1148 18 h89 kb_2456_1148
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1166 58 h90 kb_2456_1166
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1224 26 h91 kb_2456_1224
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1250 30 h92 kb_2456_1250
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1280 20 h93 kb_2456_1280
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1300 12 h94 kb_2456_1300
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1312 6 h95 kb_2456_1312
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1318 4 h96 kb_2456_1318
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1322 81 h97 kb_2456_1322
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1403 14 h98 kb_2456_1403
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1417 2 h99 kb_2456_1417
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1419 1 h100 kb_2456_1419
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1420 8 h101 kb_2456_1420
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1428 1 h102 kb_2456_1428
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1429 26 h103 kb_2456_1429
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1455 13 h104 kb_2456_1455
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1468 19 h105 kb_2456_1468
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1487 50 h106 kb_2456_1487
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1537 66 h107 kb_2456_1537
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1603 4 h108 kb_2456_1603
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1607 11 h109 kb_2456_1607
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1618 15 h110 kb_2456_1618
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1633 13 h111 kb_2456_1633
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1646 6 h112 kb_2456_1646
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1652 2 h113 kb_2456_1652
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1654 1 h114 kb_2456_1654
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1655 1 h115 kb_2456_1655
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1656 2 h116 kb_2456_1656
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1658 2 h117 kb_2456_1658
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1660 1 h118 kb_2456_1660
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1661 4 h119 kb_2456_1661
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1665 1 h120 kb_2456_1665
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1669 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1666 3 h121 kb_2456_1666
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1671 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1669 2 h122 kb_2456_1669
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1671 1 h123 kb_2456_1671
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1674 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1672 2 h124 kb_2456_1672
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1674 13 h125 kb_2456_1674
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1687 5 h126 kb_2456_1687
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1692 1 h127 kb_2456_1692
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2456.lits.getD i 0)) 0 1693 2 h128 kb_2456_1693
    exact h129
  have hg : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1695 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 5 = true := kg_2456_0
    have h1 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 6 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 5 1 h0 kg_2456_5
    have h2 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 8 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 6 2 h1 kg_2456_6
    have h3 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 12 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 8 4 h2 kg_2456_8
    have h4 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 14 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 12 2 h3 kg_2456_12
    have h5 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 19 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 14 5 h4 kg_2456_14
    have h6 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 28 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 19 9 h5 kg_2456_19
    have h7 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 30 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 28 2 h6 kg_2456_28
    have h8 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 32 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 30 2 h7 kg_2456_30
    have h9 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 33 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 32 1 h8 kg_2456_32
    have h10 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 35 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 33 2 h9 kg_2456_33
    have h11 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 45 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 35 10 h10 kg_2456_35
    have h12 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 47 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 45 2 h11 kg_2456_45
    have h13 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 48 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 47 1 h12 kg_2456_47
    have h14 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 59 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 48 11 h13 kg_2456_48
    have h15 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 61 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 59 2 h14 kg_2456_59
    have h16 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 62 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 61 1 h15 kg_2456_61
    have h17 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 70 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 62 8 h16 kg_2456_62
    have h18 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 72 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 70 2 h17 kg_2456_70
    have h19 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 73 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 72 1 h18 kg_2456_72
    have h20 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 81 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 73 8 h19 kg_2456_73
    have h21 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 82 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 81 1 h20 kg_2456_81
    have h22 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 93 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 82 11 h21 kg_2456_82
    have h23 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 122 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 93 29 h22 kg_2456_93
    have h24 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 124 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 122 2 h23 kg_2456_122
    have h25 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 130 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 124 6 h24 kg_2456_124
    have h26 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 132 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 130 2 h25 kg_2456_130
    have h27 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 172 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 132 40 h26 kg_2456_132
    have h28 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 199 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 172 27 h27 kg_2456_172
    have h29 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 203 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 199 4 h28 kg_2456_199
    have h30 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 219 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 203 16 h29 kg_2456_203
    have h31 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 221 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 219 2 h30 kg_2456_219
    have h32 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 222 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 221 1 h31 kg_2456_221
    have h33 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 223 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 222 1 h32 kg_2456_222
    have h34 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 229 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 223 6 h33 kg_2456_223
    have h35 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 231 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 229 2 h34 kg_2456_229
    have h36 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 233 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 231 2 h35 kg_2456_231
    have h37 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 237 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 233 4 h36 kg_2456_233
    have h38 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 239 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 237 2 h37 kg_2456_237
    have h39 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 244 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 239 5 h38 kg_2456_239
    have h40 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 289 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 244 45 h39 kg_2456_244
    have h41 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 367 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 289 78 h40 kg_2456_289
    have h42 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 370 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 367 3 h41 kg_2456_367
    have h43 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 377 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 370 7 h42 kg_2456_370
    have h44 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 402 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 377 25 h43 kg_2456_377
    have h45 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 408 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 402 6 h44 kg_2456_402
    have h46 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 410 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 408 2 h45 kg_2456_408
    have h47 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 460 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 410 50 h46 kg_2456_410
    have h48 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 500 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 460 40 h47 kg_2456_460
    have h49 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 501 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 500 1 h48 kg_2456_500
    have h50 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 502 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 501 1 h49 kg_2456_501
    have h51 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 507 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 502 5 h50 kg_2456_502
    have h52 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 519 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 507 12 h51 kg_2456_507
    have h53 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 539 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 519 20 h52 kg_2456_519
    have h54 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 545 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 539 6 h53 kg_2456_539
    have h55 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 549 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 545 4 h54 kg_2456_545
    have h56 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 626 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 549 77 h55 kg_2456_549
    have h57 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 629 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 626 3 h56 kg_2456_626
    have h58 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 637 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 629 8 h57 kg_2456_629
    have h59 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 639 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 637 2 h58 kg_2456_637
    have h60 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 640 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 639 1 h59 kg_2456_639
    have h61 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 646 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 640 6 h60 kg_2456_640
    have h62 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 692 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 646 46 h61 kg_2456_646
    have h63 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 766 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 692 74 h62 kg_2456_692
    have h64 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 770 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 766 4 h63 kg_2456_766
    have h65 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 798 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 770 28 h64 kg_2456_770
    have h66 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 804 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 798 6 h65 kg_2456_798
    have h67 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 806 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 804 2 h66 kg_2456_804
    have h68 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 856 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 806 50 h67 kg_2456_806
    have h69 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 895 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 856 39 h68 kg_2456_856
    have h70 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 900 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 895 5 h69 kg_2456_895
    have h71 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 920 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 900 20 h70 kg_2456_900
    have h72 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 922 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 920 2 h71 kg_2456_920
    have h73 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 940 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 922 18 h72 kg_2456_922
    have h74 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 942 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 940 2 h73 kg_2456_940
    have h75 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 974 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 942 32 h74 kg_2456_942
    have h76 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1002 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 974 28 h75 kg_2456_974
    have h77 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1004 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1002 2 h76 kg_2456_1002
    have h78 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1015 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1004 11 h77 kg_2456_1004
    have h79 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1036 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1015 21 h78 kg_2456_1015
    have h80 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1084 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1036 48 h79 kg_2456_1036
    have h81 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1118 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1084 34 h80 kg_2456_1084
    have h82 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1120 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1118 2 h81 kg_2456_1118
    have h83 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1124 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1120 4 h82 kg_2456_1120
    have h84 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1125 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1124 1 h83 kg_2456_1124
    have h85 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1126 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1125 1 h84 kg_2456_1125
    have h86 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1127 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1126 1 h85 kg_2456_1126
    have h87 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1128 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1127 1 h86 kg_2456_1127
    have h88 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1132 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1128 4 h87 kg_2456_1128
    have h89 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1148 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1132 16 h88 kg_2456_1132
    have h90 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1166 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1148 18 h89 kg_2456_1148
    have h91 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1224 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1166 58 h90 kg_2456_1166
    have h92 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1250 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1224 26 h91 kg_2456_1224
    have h93 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1280 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1250 30 h92 kg_2456_1250
    have h94 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1300 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1280 20 h93 kg_2456_1280
    have h95 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1312 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1300 12 h94 kg_2456_1300
    have h96 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1318 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1312 6 h95 kg_2456_1312
    have h97 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1322 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1318 4 h96 kg_2456_1318
    have h98 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1403 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1322 81 h97 kg_2456_1322
    have h99 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1417 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1403 14 h98 kg_2456_1403
    have h100 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1419 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1417 2 h99 kg_2456_1417
    have h101 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1420 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1419 1 h100 kg_2456_1419
    have h102 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1428 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1420 8 h101 kg_2456_1420
    have h103 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1429 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1428 1 h102 kg_2456_1428
    have h104 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1455 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1429 26 h103 kg_2456_1429
    have h105 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1468 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1455 13 h104 kg_2456_1455
    have h106 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1487 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1468 19 h105 kg_2456_1468
    have h107 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1537 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1487 50 h106 kg_2456_1487
    have h108 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1603 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1537 66 h107 kg_2456_1537
    have h109 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1607 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1603 4 h108 kg_2456_1603
    have h110 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1618 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1607 11 h109 kg_2456_1607
    have h111 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1633 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1618 15 h110 kg_2456_1618
    have h112 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1646 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1633 13 h111 kg_2456_1633
    have h113 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1652 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1646 6 h112 kg_2456_1646
    have h114 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1654 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1652 2 h113 kg_2456_1652
    have h115 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1655 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1654 1 h114 kg_2456_1654
    have h116 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1656 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1655 1 h115 kg_2456_1655
    have h117 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1658 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1656 2 h116 kg_2456_1656
    have h118 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1660 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1658 2 h117 kg_2456_1658
    have h119 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1661 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1660 1 h118 kg_2456_1660
    have h120 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1665 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1661 4 h119 kg_2456_1661
    have h121 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1666 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1665 1 h120 kg_2456_1665
    have h122 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1669 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1666 3 h121 kg_2456_1666
    have h123 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1671 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1669 2 h122 kg_2456_1669
    have h124 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1672 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1671 1 h123 kg_2456_1671
    have h125 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1674 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1672 2 h124 kg_2456_1672
    have h126 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1687 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1674 13 h125 kg_2456_1674
    have h127 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1692 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1687 5 h126 kg_2456_1687
    have h128 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1693 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1692 1 h127 kg_2456_1692
    have h129 : IPChk.allR (Pts.glueIB K2456.lits KW_2456) 0 1695 = true := IPChk.allR_join (Pts.glueIB K2456.lits KW_2456) 0 1693 2 h128 kg_2456_1693
    exact h129
  have hlen : K2456.lits.length = 1695 := by decide
  intro k h1 h2
  obtain rfl : k = 2456 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2456) K2456.lits KW_2456
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_429 : ∀ k, 2457 ≤ k → k < 2458 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2457 JW_2457 2457 1 jr_2457
theorem jr6_430 : ∀ k, 2458 ≤ k → k < 2459 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1088 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 4 = true := kb_2458_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 4 3 h0 kb_2458_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 7 4 h1 kb_2458_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 11 2 h2 kb_2458_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 13 8 h3 kb_2458_13
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 21 8 h4 kb_2458_21
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 29 1 h5 kb_2458_29
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 30 1 h6 kb_2458_30
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 31 7 h7 kb_2458_31
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 38 2 h8 kb_2458_38
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 40 2 h9 kb_2458_40
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 42 4 h10 kb_2458_42
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 46 10 h11 kb_2458_46
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 56 1 h12 kb_2458_56
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 57 1 h13 kb_2458_57
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 58 1 h14 kb_2458_58
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 59 9 h15 kb_2458_59
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 68 2 h16 kb_2458_68
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 70 1 h17 kb_2458_70
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 71 8 h18 kb_2458_71
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 79 4 h19 kb_2458_79
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 83 9 h20 kb_2458_83
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 92 23 h21 kb_2458_92
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 115 2 h22 kb_2458_115
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 117 6 h23 kb_2458_117
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 123 2 h24 kb_2458_123
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 125 17 h25 kb_2458_125
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 142 6 h26 kb_2458_142
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 148 2 h27 kb_2458_148
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 150 16 h28 kb_2458_150
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 166 1 h29 kb_2458_166
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 167 3 h30 kb_2458_167
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 170 3 h31 kb_2458_170
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 173 6 h32 kb_2458_173
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 179 26 h33 kb_2458_179
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 205 6 h34 kb_2458_205
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 211 2 h35 kb_2458_211
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 213 22 h36 kb_2458_213
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 235 45 h37 kb_2458_235
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 280 5 h38 kb_2458_280
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 285 9 h39 kb_2458_285
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 294 2 h40 kb_2458_294
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 296 2 h41 kb_2458_296
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 298 3 h42 kb_2458_298
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 301 7 h43 kb_2458_301
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 308 25 h44 kb_2458_308
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 333 6 h45 kb_2458_333
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 339 4 h46 kb_2458_339
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 343 82 h47 kb_2458_343
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 425 8 h48 kb_2458_425
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 433 1 h49 kb_2458_433
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 434 42 h50 kb_2458_434
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 476 77 h51 kb_2458_476
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 553 5 h52 kb_2458_553
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 558 27 h53 kb_2458_558
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 585 6 h54 kb_2458_585
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 593 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 591 2 h55 kb_2458_591
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 593 51 h56 kb_2458_593
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 644 19 h57 kb_2458_644
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 673 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 663 10 h58 kb_2458_663
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 673 18 h59 kb_2458_673
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 691 4 h60 kb_2458_691
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 695 2 h61 kb_2458_695
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 697 18 h62 kb_2458_697
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 715 2 h63 kb_2458_715
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 750 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 717 33 h64 kb_2458_717
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 750 35 h65 kb_2458_750
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 785 1 h66 kb_2458_785
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 786 16 h67 kb_2458_786
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 807 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 802 5 h68 kb_2458_802
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 807 1 h69 kb_2458_807
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 816 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 808 8 h70 kb_2458_808
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 817 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 816 1 h71 kb_2458_816
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 817 7 h72 kb_2458_817
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 824 17 h73 kb_2458_824
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 849 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 841 8 h74 kb_2458_841
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 850 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 849 1 h75 kb_2458_849
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 852 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 850 2 h76 kb_2458_850
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 853 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 852 1 h77 kb_2458_852
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 854 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 853 1 h78 kb_2458_853
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 857 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 854 3 h79 kb_2458_854
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 866 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 857 9 h80 kb_2458_857
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 866 12 h81 kb_2458_866
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 896 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 878 18 h82 kb_2458_878
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 898 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 896 2 h83 kb_2458_896
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 898 1 h84 kb_2458_898
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 902 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 899 3 h85 kb_2458_899
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 904 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 902 2 h86 kb_2458_902
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 904 17 h87 kb_2458_904
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 925 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 921 4 h88 kb_2458_921
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 926 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 925 1 h89 kb_2458_925
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 926 9 h90 kb_2458_926
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 935 1 h91 kb_2458_935
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 936 7 h92 kb_2458_936
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 967 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 943 24 h93 kb_2458_943
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 967 5 h94 kb_2458_967
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 972 33 h95 kb_2458_972
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1023 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1005 18 h96 kb_2458_1005
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1023 20 h97 kb_2458_1023
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1044 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1043 1 h98 kb_2458_1043
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1047 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1044 3 h99 kb_2458_1044
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1049 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1047 2 h100 kb_2458_1047
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1050 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1049 1 h101 kb_2458_1049
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1052 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1050 2 h102 kb_2458_1050
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1053 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1052 1 h103 kb_2458_1052
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1067 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1053 14 h104 kb_2458_1053
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1084 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1067 17 h105 kb_2458_1067
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1088 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 0 1084 4 h106 kb_2458_1084
    exact h107
  have hg : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1088 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 4 = true := kg_2458_0
    have h1 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 7 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 4 3 h0 kg_2458_4
    have h2 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 11 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 7 4 h1 kg_2458_7
    have h3 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 13 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 11 2 h2 kg_2458_11
    have h4 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 21 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 13 8 h3 kg_2458_13
    have h5 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 29 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 21 8 h4 kg_2458_21
    have h6 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 30 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 29 1 h5 kg_2458_29
    have h7 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 31 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 30 1 h6 kg_2458_30
    have h8 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 38 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 31 7 h7 kg_2458_31
    have h9 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 40 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 38 2 h8 kg_2458_38
    have h10 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 42 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 40 2 h9 kg_2458_40
    have h11 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 46 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 42 4 h10 kg_2458_42
    have h12 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 56 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 46 10 h11 kg_2458_46
    have h13 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 57 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 56 1 h12 kg_2458_56
    have h14 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 58 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 57 1 h13 kg_2458_57
    have h15 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 59 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 58 1 h14 kg_2458_58
    have h16 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 68 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 59 9 h15 kg_2458_59
    have h17 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 70 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 68 2 h16 kg_2458_68
    have h18 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 71 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 70 1 h17 kg_2458_70
    have h19 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 79 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 71 8 h18 kg_2458_71
    have h20 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 83 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 79 4 h19 kg_2458_79
    have h21 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 92 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 83 9 h20 kg_2458_83
    have h22 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 115 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 92 23 h21 kg_2458_92
    have h23 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 117 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 115 2 h22 kg_2458_115
    have h24 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 123 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 117 6 h23 kg_2458_117
    have h25 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 125 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 123 2 h24 kg_2458_123
    have h26 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 142 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 125 17 h25 kg_2458_125
    have h27 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 148 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 142 6 h26 kg_2458_142
    have h28 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 150 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 148 2 h27 kg_2458_148
    have h29 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 166 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 150 16 h28 kg_2458_150
    have h30 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 167 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 166 1 h29 kg_2458_166
    have h31 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 170 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 167 3 h30 kg_2458_167
    have h32 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 173 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 170 3 h31 kg_2458_170
    have h33 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 179 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 173 6 h32 kg_2458_173
    have h34 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 205 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 179 26 h33 kg_2458_179
    have h35 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 211 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 205 6 h34 kg_2458_205
    have h36 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 213 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 211 2 h35 kg_2458_211
    have h37 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 235 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 213 22 h36 kg_2458_213
    have h38 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 280 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 235 45 h37 kg_2458_235
    have h39 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 285 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 280 5 h38 kg_2458_280
    have h40 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 294 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 285 9 h39 kg_2458_285
    have h41 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 296 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 294 2 h40 kg_2458_294
    have h42 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 298 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 296 2 h41 kg_2458_296
    have h43 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 301 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 298 3 h42 kg_2458_298
    have h44 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 308 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 301 7 h43 kg_2458_301
    have h45 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 333 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 308 25 h44 kg_2458_308
    have h46 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 339 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 333 6 h45 kg_2458_333
    have h47 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 343 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 339 4 h46 kg_2458_339
    have h48 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 425 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 343 82 h47 kg_2458_343
    have h49 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 433 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 425 8 h48 kg_2458_425
    have h50 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 434 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 433 1 h49 kg_2458_433
    have h51 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 476 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 434 42 h50 kg_2458_434
    have h52 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 553 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 476 77 h51 kg_2458_476
    have h53 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 558 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 553 5 h52 kg_2458_553
    have h54 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 585 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 558 27 h53 kg_2458_558
    have h55 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 591 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 585 6 h54 kg_2458_585
    have h56 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 593 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 591 2 h55 kg_2458_591
    have h57 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 644 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 593 51 h56 kg_2458_593
    have h58 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 663 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 644 19 h57 kg_2458_644
    have h59 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 673 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 663 10 h58 kg_2458_663
    have h60 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 691 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 673 18 h59 kg_2458_673
    have h61 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 695 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 691 4 h60 kg_2458_691
    have h62 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 697 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 695 2 h61 kg_2458_695
    have h63 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 715 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 697 18 h62 kg_2458_697
    have h64 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 717 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 715 2 h63 kg_2458_715
    have h65 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 750 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 717 33 h64 kg_2458_717
    have h66 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 785 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 750 35 h65 kg_2458_750
    have h67 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 786 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 785 1 h66 kg_2458_785
    have h68 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 802 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 786 16 h67 kg_2458_786
    have h69 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 807 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 802 5 h68 kg_2458_802
    have h70 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 808 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 807 1 h69 kg_2458_807
    have h71 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 816 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 808 8 h70 kg_2458_808
    have h72 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 817 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 816 1 h71 kg_2458_816
    have h73 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 824 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 817 7 h72 kg_2458_817
    have h74 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 841 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 824 17 h73 kg_2458_824
    have h75 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 849 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 841 8 h74 kg_2458_841
    have h76 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 850 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 849 1 h75 kg_2458_849
    have h77 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 852 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 850 2 h76 kg_2458_850
    have h78 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 853 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 852 1 h77 kg_2458_852
    have h79 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 854 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 853 1 h78 kg_2458_853
    have h80 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 857 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 854 3 h79 kg_2458_854
    have h81 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 866 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 857 9 h80 kg_2458_857
    have h82 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 878 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 866 12 h81 kg_2458_866
    have h83 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 896 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 878 18 h82 kg_2458_878
    have h84 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 898 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 896 2 h83 kg_2458_896
    have h85 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 899 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 898 1 h84 kg_2458_898
    have h86 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 902 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 899 3 h85 kg_2458_899
    have h87 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 904 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 902 2 h86 kg_2458_902
    have h88 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 921 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 904 17 h87 kg_2458_904
    have h89 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 925 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 921 4 h88 kg_2458_921
    have h90 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 926 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 925 1 h89 kg_2458_925
    have h91 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 935 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 926 9 h90 kg_2458_926
    have h92 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 936 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 935 1 h91 kg_2458_935
    have h93 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 943 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 936 7 h92 kg_2458_936
    have h94 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 967 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 943 24 h93 kg_2458_943
    have h95 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 972 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 967 5 h94 kg_2458_967
    have h96 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1005 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 972 33 h95 kg_2458_972
    have h97 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1023 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1005 18 h96 kg_2458_1005
    have h98 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1043 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1023 20 h97 kg_2458_1023
    have h99 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1044 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1043 1 h98 kg_2458_1043
    have h100 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1047 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1044 3 h99 kg_2458_1044
    have h101 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1049 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1047 2 h100 kg_2458_1047
    have h102 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1050 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1049 1 h101 kg_2458_1049
    have h103 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1052 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1050 2 h102 kg_2458_1050
    have h104 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1053 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1052 1 h103 kg_2458_1052
    have h105 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1067 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1053 14 h104 kg_2458_1053
    have h106 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1084 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1067 17 h105 kg_2458_1067
    have h107 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 0 1088 = true := IPChk.allR_join (Pts.glueIB K2458.lits KW_2458) 0 1084 4 h106 kg_2458_1084
    exact h107
  have hlen : K2458.lits.length = 1088 := by decide
  intro k h1 h2
  obtain rfl : k = 2458 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2458) K2458.lits KW_2458
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_431 : ∀ k, 2459 ≤ k → k < 2460 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2459 JW_2459 2459 1 jr_2459
theorem jr6_432 : ∀ k, 2460 ≤ k → k < 2461 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1698 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 2 = true := kb_2460_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 2 3 h0 kb_2460_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 5 3 h1 kb_2460_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 8 3 h2 kb_2460_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 11 4 h3 kb_2460_11
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 15 9 h4 kb_2460_15
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 24 1 h5 kb_2460_24
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 25 2 h6 kb_2460_25
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 27 1 h7 kb_2460_27
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 28 2 h8 kb_2460_28
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 30 10 h9 kb_2460_30
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 40 2 h10 kb_2460_40
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 42 1 h11 kb_2460_42
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 43 1 h12 kb_2460_43
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 44 9 h13 kb_2460_44
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 53 4 h14 kb_2460_53
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 57 1 h15 kb_2460_57
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 58 8 h16 kb_2460_58
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 66 1 h17 kb_2460_66
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 67 8 h18 kb_2460_67
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 75 1 h19 kb_2460_75
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 76 10 h20 kb_2460_76
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 86 29 h21 kb_2460_86
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 115 2 h22 kb_2460_115
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 117 6 h23 kb_2460_117
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 123 2 h24 kb_2460_123
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 125 48 h25 kb_2460_125
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 173 22 h26 kb_2460_173
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 195 4 h27 kb_2460_195
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 199 16 h28 kb_2460_199
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 215 2 h29 kb_2460_215
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 217 1 h30 kb_2460_217
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 218 6 h31 kb_2460_218
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 224 4 h32 kb_2460_224
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 228 5 h33 kb_2460_228
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 233 1 h34 kb_2460_233
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 234 6 h35 kb_2460_234
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 240 45 h36 kb_2460_240
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 285 79 h37 kb_2460_285
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 364 7 h38 kb_2460_364
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 371 4 h39 kb_2460_371
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 375 28 h40 kb_2460_375
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 403 6 h41 kb_2460_403
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 409 2 h42 kb_2460_409
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 411 46 h43 kb_2460_411
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 457 43 h44 kb_2460_457
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 500 4 h45 kb_2460_500
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 504 2 h46 kb_2460_504
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 506 1 h47 kb_2460_506
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 507 2 h48 kb_2460_507
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 509 2 h49 kb_2460_509
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 511 3 h50 kb_2460_511
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 522 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 514 8 h51 kb_2460_514
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 522 24 h52 kb_2460_522
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 546 6 h53 kb_2460_546
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 552 2 h54 kb_2460_552
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 554 52 h55 kb_2460_554
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 606 32 h56 kb_2460_606
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 638 1 h57 kb_2460_638
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 639 7 h58 kb_2460_639
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 646 2 h59 kb_2460_646
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 649 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 648 1 h60 kb_2460_648
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 649 9 h61 kb_2460_649
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 658 113 h62 kb_2460_658
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 777 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 771 6 h63 kb_2460_771
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 803 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 777 26 h64 kb_2460_777
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 809 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 803 6 h65 kb_2460_803
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 809 2 h66 kb_2460_809
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 864 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 811 53 h67 kb_2460_811
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 864 35 h68 kb_2460_864
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 899 4 h69 kb_2460_899
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 905 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 903 2 h70 kb_2460_903
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 909 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 905 4 h71 kb_2460_905
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 910 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 909 1 h72 kb_2460_909
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 910 17 h73 kb_2460_910
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 929 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 927 2 h74 kb_2460_927
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 961 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 929 32 h75 kb_2460_929
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 961 28 h76 kb_2460_961
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 990 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 989 1 h77 kb_2460_989
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 993 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 990 3 h78 kb_2460_990
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 993 29 h79 kb_2460_993
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1024 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1022 2 h80 kb_2460_1022
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1030 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1024 6 h81 kb_2460_1024
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1034 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1030 4 h82 kb_2460_1030
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1034 75 h83 kb_2460_1034
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1109 3 h84 kb_2460_1109
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1112 29 h85 kb_2460_1112
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1141 2 h86 kb_2460_1141
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1143 21 h87 kb_2460_1143
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1164 48 h88 kb_2460_1164
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1212 2 h89 kb_2460_1212
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1214 8 h90 kb_2460_1214
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1222 29 h91 kb_2460_1222
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1251 2 h92 kb_2460_1251
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1253 6 h93 kb_2460_1253
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1259 2 h94 kb_2460_1259
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1261 67 h95 kb_2460_1261
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1349 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1328 21 h96 kb_2460_1328
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1349 20 h97 kb_2460_1349
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1369 5 h98 kb_2460_1369
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1374 10 h99 kb_2460_1374
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1384 1 h100 kb_2460_1384
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1385 2 h101 kb_2460_1385
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1387 1 h102 kb_2460_1387
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1388 15 h103 kb_2460_1388
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1403 2 h104 kb_2460_1403
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1405 1 h105 kb_2460_1405
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1406 8 h106 kb_2460_1406
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1414 1 h107 kb_2460_1414
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1415 28 h108 kb_2460_1415
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1443 1 h109 kb_2460_1443
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1444 25 h110 kb_2460_1444
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1475 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1469 6 h111 kb_2460_1469
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1475 6 h112 kb_2460_1475
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1481 8 h113 kb_2460_1481
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1489 72 h114 kb_2460_1489
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1561 2 h115 kb_2460_1561
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1563 12 h116 kb_2460_1563
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1575 1 h117 kb_2460_1575
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1576 3 h118 kb_2460_1576
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1579 1 h119 kb_2460_1579
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1580 11 h120 kb_2460_1580
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1593 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1591 2 h121 kb_2460_1591
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1593 3 h122 kb_2460_1593
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1605 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1596 9 h123 kb_2460_1596
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1605 13 h124 kb_2460_1605
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1630 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1618 12 h125 kb_2460_1618
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1637 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1630 7 h126 kb_2460_1630
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1637 6 h127 kb_2460_1637
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1647 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1643 4 h128 kb_2460_1643
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1647 5 h129 kb_2460_1647
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1652 4 h130 kb_2460_1652
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1659 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1656 3 h131 kb_2460_1656
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1659 1 h132 kb_2460_1659
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1660 1 h133 kb_2460_1660
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1661 2 h134 kb_2460_1661
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1663 2 h135 kb_2460_1663
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1667 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1665 2 h136 kb_2460_1665
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1667 10 h137 kb_2460_1667
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1677 4 h138 kb_2460_1677
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1681 1 h139 kb_2460_1681
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1682 1 h140 kb_2460_1682
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1683 1 h141 kb_2460_1683
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1684 1 h142 kb_2460_1684
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1685 1 h143 kb_2460_1685
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1686 2 h144 kb_2460_1686
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1688 8 h145 kb_2460_1688
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1696 1 h146 kb_2460_1696
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1698 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 0 1697 1 h147 kb_2460_1697
    exact h148
  have hg : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1698 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 2 = true := kg_2460_0
    have h1 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 5 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 2 3 h0 kg_2460_2
    have h2 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 8 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 5 3 h1 kg_2460_5
    have h3 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 11 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 8 3 h2 kg_2460_8
    have h4 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 15 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 11 4 h3 kg_2460_11
    have h5 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 24 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 15 9 h4 kg_2460_15
    have h6 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 25 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 24 1 h5 kg_2460_24
    have h7 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 27 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 25 2 h6 kg_2460_25
    have h8 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 28 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 27 1 h7 kg_2460_27
    have h9 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 30 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 28 2 h8 kg_2460_28
    have h10 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 40 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 30 10 h9 kg_2460_30
    have h11 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 42 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 40 2 h10 kg_2460_40
    have h12 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 43 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 42 1 h11 kg_2460_42
    have h13 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 44 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 43 1 h12 kg_2460_43
    have h14 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 53 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 44 9 h13 kg_2460_44
    have h15 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 57 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 53 4 h14 kg_2460_53
    have h16 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 58 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 57 1 h15 kg_2460_57
    have h17 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 66 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 58 8 h16 kg_2460_58
    have h18 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 67 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 66 1 h17 kg_2460_66
    have h19 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 75 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 67 8 h18 kg_2460_67
    have h20 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 76 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 75 1 h19 kg_2460_75
    have h21 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 86 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 76 10 h20 kg_2460_76
    have h22 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 115 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 86 29 h21 kg_2460_86
    have h23 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 117 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 115 2 h22 kg_2460_115
    have h24 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 123 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 117 6 h23 kg_2460_117
    have h25 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 125 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 123 2 h24 kg_2460_123
    have h26 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 173 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 125 48 h25 kg_2460_125
    have h27 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 195 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 173 22 h26 kg_2460_173
    have h28 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 199 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 195 4 h27 kg_2460_195
    have h29 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 215 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 199 16 h28 kg_2460_199
    have h30 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 217 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 215 2 h29 kg_2460_215
    have h31 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 218 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 217 1 h30 kg_2460_217
    have h32 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 224 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 218 6 h31 kg_2460_218
    have h33 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 228 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 224 4 h32 kg_2460_224
    have h34 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 233 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 228 5 h33 kg_2460_228
    have h35 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 234 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 233 1 h34 kg_2460_233
    have h36 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 240 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 234 6 h35 kg_2460_234
    have h37 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 285 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 240 45 h36 kg_2460_240
    have h38 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 364 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 285 79 h37 kg_2460_285
    have h39 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 371 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 364 7 h38 kg_2460_364
    have h40 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 375 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 371 4 h39 kg_2460_371
    have h41 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 403 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 375 28 h40 kg_2460_375
    have h42 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 409 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 403 6 h41 kg_2460_403
    have h43 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 411 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 409 2 h42 kg_2460_409
    have h44 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 457 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 411 46 h43 kg_2460_411
    have h45 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 500 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 457 43 h44 kg_2460_457
    have h46 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 504 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 500 4 h45 kg_2460_500
    have h47 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 506 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 504 2 h46 kg_2460_504
    have h48 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 507 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 506 1 h47 kg_2460_506
    have h49 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 509 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 507 2 h48 kg_2460_507
    have h50 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 511 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 509 2 h49 kg_2460_509
    have h51 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 514 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 511 3 h50 kg_2460_511
    have h52 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 522 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 514 8 h51 kg_2460_514
    have h53 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 546 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 522 24 h52 kg_2460_522
    have h54 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 552 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 546 6 h53 kg_2460_546
    have h55 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 554 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 552 2 h54 kg_2460_552
    have h56 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 606 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 554 52 h55 kg_2460_554
    have h57 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 638 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 606 32 h56 kg_2460_606
    have h58 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 639 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 638 1 h57 kg_2460_638
    have h59 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 646 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 639 7 h58 kg_2460_639
    have h60 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 648 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 646 2 h59 kg_2460_646
    have h61 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 649 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 648 1 h60 kg_2460_648
    have h62 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 658 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 649 9 h61 kg_2460_649
    have h63 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 771 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 658 113 h62 kg_2460_658
    have h64 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 777 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 771 6 h63 kg_2460_771
    have h65 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 803 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 777 26 h64 kg_2460_777
    have h66 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 809 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 803 6 h65 kg_2460_803
    have h67 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 811 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 809 2 h66 kg_2460_809
    have h68 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 864 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 811 53 h67 kg_2460_811
    have h69 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 899 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 864 35 h68 kg_2460_864
    have h70 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 903 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 899 4 h69 kg_2460_899
    have h71 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 905 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 903 2 h70 kg_2460_903
    have h72 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 909 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 905 4 h71 kg_2460_905
    have h73 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 910 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 909 1 h72 kg_2460_909
    have h74 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 927 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 910 17 h73 kg_2460_910
    have h75 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 929 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 927 2 h74 kg_2460_927
    have h76 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 961 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 929 32 h75 kg_2460_929
    have h77 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 989 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 961 28 h76 kg_2460_961
    have h78 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 990 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 989 1 h77 kg_2460_989
    have h79 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 993 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 990 3 h78 kg_2460_990
    have h80 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1022 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 993 29 h79 kg_2460_993
    have h81 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1024 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1022 2 h80 kg_2460_1022
    have h82 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1030 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1024 6 h81 kg_2460_1024
    have h83 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1034 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1030 4 h82 kg_2460_1030
    have h84 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1109 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1034 75 h83 kg_2460_1034
    have h85 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1112 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1109 3 h84 kg_2460_1109
    have h86 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1141 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1112 29 h85 kg_2460_1112
    have h87 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1143 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1141 2 h86 kg_2460_1141
    have h88 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1164 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1143 21 h87 kg_2460_1143
    have h89 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1212 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1164 48 h88 kg_2460_1164
    have h90 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1214 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1212 2 h89 kg_2460_1212
    have h91 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1222 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1214 8 h90 kg_2460_1214
    have h92 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1251 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1222 29 h91 kg_2460_1222
    have h93 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1253 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1251 2 h92 kg_2460_1251
    have h94 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1259 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1253 6 h93 kg_2460_1253
    have h95 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1261 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1259 2 h94 kg_2460_1259
    have h96 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1328 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1261 67 h95 kg_2460_1261
    have h97 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1349 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1328 21 h96 kg_2460_1328
    have h98 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1369 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1349 20 h97 kg_2460_1349
    have h99 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1374 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1369 5 h98 kg_2460_1369
    have h100 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1384 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1374 10 h99 kg_2460_1374
    have h101 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1385 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1384 1 h100 kg_2460_1384
    have h102 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1387 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1385 2 h101 kg_2460_1385
    have h103 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1388 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1387 1 h102 kg_2460_1387
    have h104 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1403 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1388 15 h103 kg_2460_1388
    have h105 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1405 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1403 2 h104 kg_2460_1403
    have h106 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1406 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1405 1 h105 kg_2460_1405
    have h107 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1414 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1406 8 h106 kg_2460_1406
    have h108 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1415 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1414 1 h107 kg_2460_1414
    have h109 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1443 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1415 28 h108 kg_2460_1415
    have h110 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1444 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1443 1 h109 kg_2460_1443
    have h111 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1469 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1444 25 h110 kg_2460_1444
    have h112 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1475 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1469 6 h111 kg_2460_1469
    have h113 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1481 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1475 6 h112 kg_2460_1475
    have h114 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1489 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1481 8 h113 kg_2460_1481
    have h115 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1561 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1489 72 h114 kg_2460_1489
    have h116 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1563 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1561 2 h115 kg_2460_1561
    have h117 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1575 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1563 12 h116 kg_2460_1563
    have h118 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1576 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1575 1 h117 kg_2460_1575
    have h119 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1579 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1576 3 h118 kg_2460_1576
    have h120 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1580 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1579 1 h119 kg_2460_1579
    have h121 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1591 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1580 11 h120 kg_2460_1580
    have h122 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1593 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1591 2 h121 kg_2460_1591
    have h123 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1596 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1593 3 h122 kg_2460_1593
    have h124 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1605 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1596 9 h123 kg_2460_1596
    have h125 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1618 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1605 13 h124 kg_2460_1605
    have h126 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1630 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1618 12 h125 kg_2460_1618
    have h127 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1637 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1630 7 h126 kg_2460_1630
    have h128 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1643 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1637 6 h127 kg_2460_1637
    have h129 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1647 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1643 4 h128 kg_2460_1643
    have h130 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1652 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1647 5 h129 kg_2460_1647
    have h131 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1656 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1652 4 h130 kg_2460_1652
    have h132 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1659 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1656 3 h131 kg_2460_1656
    have h133 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1660 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1659 1 h132 kg_2460_1659
    have h134 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1661 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1660 1 h133 kg_2460_1660
    have h135 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1663 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1661 2 h134 kg_2460_1661
    have h136 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1665 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1663 2 h135 kg_2460_1663
    have h137 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1667 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1665 2 h136 kg_2460_1665
    have h138 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1677 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1667 10 h137 kg_2460_1667
    have h139 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1681 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1677 4 h138 kg_2460_1677
    have h140 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1682 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1681 1 h139 kg_2460_1681
    have h141 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1683 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1682 1 h140 kg_2460_1682
    have h142 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1684 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1683 1 h141 kg_2460_1683
    have h143 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1685 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1684 1 h142 kg_2460_1684
    have h144 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1686 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1685 1 h143 kg_2460_1685
    have h145 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1688 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1686 2 h144 kg_2460_1686
    have h146 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1696 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1688 8 h145 kg_2460_1688
    have h147 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1697 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1696 1 h146 kg_2460_1696
    have h148 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 0 1698 = true := IPChk.allR_join (Pts.glueIB K2460.lits KW_2460) 0 1697 1 h147 kg_2460_1697
    exact h148
  have hlen : K2460.lits.length = 1698 := by decide
  intro k h1 h2
  obtain rfl : k = 2460 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2460) K2460.lits KW_2460
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_433 : ∀ k, 2461 ≤ k → k < 2463 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2461 JW_2461 2461 2 jr_2461
theorem jr6_434 : ∀ k, 2463 ≤ k → k < 2464 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 313 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 7 = true := kb_2463_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 7 19 h0 kb_2463_7
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 26 16 h1 kb_2463_26
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 42 1 h2 kb_2463_42
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 43 1 h3 kb_2463_43
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 44 18 h4 kb_2463_44
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 62 14 h5 kb_2463_62
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 76 2 h6 kb_2463_76
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 78 34 h7 kb_2463_78
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 112 9 h8 kb_2463_112
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 121 62 h9 kb_2463_121
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 183 57 h10 kb_2463_183
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 240 3 h11 kb_2463_240
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 243 37 h12 kb_2463_243
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 280 4 h13 kb_2463_280
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 284 2 h14 kb_2463_284
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 286 2 h15 kb_2463_286
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 288 4 h16 kb_2463_288
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 292 17 h17 kb_2463_292
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2463.lits.getD i 0)) 0 309 4 h18 kb_2463_309
    exact h19
  have hg : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 313 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 7 = true := kg_2463_0
    have h1 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 26 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 7 19 h0 kg_2463_7
    have h2 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 42 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 26 16 h1 kg_2463_26
    have h3 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 43 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 42 1 h2 kg_2463_42
    have h4 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 44 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 43 1 h3 kg_2463_43
    have h5 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 62 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 44 18 h4 kg_2463_44
    have h6 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 76 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 62 14 h5 kg_2463_62
    have h7 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 78 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 76 2 h6 kg_2463_76
    have h8 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 112 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 78 34 h7 kg_2463_78
    have h9 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 121 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 112 9 h8 kg_2463_112
    have h10 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 183 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 121 62 h9 kg_2463_121
    have h11 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 240 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 183 57 h10 kg_2463_183
    have h12 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 243 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 240 3 h11 kg_2463_240
    have h13 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 280 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 243 37 h12 kg_2463_243
    have h14 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 284 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 280 4 h13 kg_2463_280
    have h15 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 286 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 284 2 h14 kg_2463_284
    have h16 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 288 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 286 2 h15 kg_2463_286
    have h17 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 292 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 288 4 h16 kg_2463_288
    have h18 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 309 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 292 17 h17 kg_2463_292
    have h19 : IPChk.allR (Pts.glueIB K2463.lits KW_2463) 0 313 = true := IPChk.allR_join (Pts.glueIB K2463.lits KW_2463) 0 309 4 h18 kg_2463_309
    exact h19
  have hlen : K2463.lits.length = 313 := by decide
  intro k h1 h2
  obtain rfl : k = 2463 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2463) K2463.lits KW_2463
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_435 : ∀ k, 2464 ≤ k → k < 2465 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 427 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 5 = true := kb_2464_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 5 8 h0 kb_2464_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 13 8 h1 kb_2464_13
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 21 1 h2 kb_2464_21
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 22 1 h3 kb_2464_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 23 8 h4 kb_2464_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 31 9 h5 kb_2464_31
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 40 21 h6 kb_2464_40
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 61 6 h7 kb_2464_61
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 67 2 h8 kb_2464_67
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 69 19 h9 kb_2464_69
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 88 6 h10 kb_2464_88
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 94 2 h11 kb_2464_94
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 96 16 h12 kb_2464_96
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 112 1 h13 kb_2464_112
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 113 7 h14 kb_2464_113
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 120 100 h15 kb_2464_120
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 220 70 h16 kb_2464_220
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 290 7 h17 kb_2464_290
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 297 2 h18 kb_2464_297
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 299 18 h19 kb_2464_299
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 317 2 h20 kb_2464_317
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 319 31 h21 kb_2464_319
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 350 30 h22 kb_2464_350
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 380 21 h23 kb_2464_380
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2464.lits.getD i 0)) 0 401 26 h24 kb_2464_401
    exact h25
  have hg : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 427 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 5 = true := kg_2464_0
    have h1 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 13 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 5 8 h0 kg_2464_5
    have h2 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 21 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 13 8 h1 kg_2464_13
    have h3 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 22 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 21 1 h2 kg_2464_21
    have h4 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 23 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 22 1 h3 kg_2464_22
    have h5 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 31 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 23 8 h4 kg_2464_23
    have h6 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 40 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 31 9 h5 kg_2464_31
    have h7 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 61 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 40 21 h6 kg_2464_40
    have h8 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 67 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 61 6 h7 kg_2464_61
    have h9 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 69 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 67 2 h8 kg_2464_67
    have h10 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 88 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 69 19 h9 kg_2464_69
    have h11 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 94 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 88 6 h10 kg_2464_88
    have h12 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 96 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 94 2 h11 kg_2464_94
    have h13 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 112 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 96 16 h12 kg_2464_96
    have h14 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 113 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 112 1 h13 kg_2464_112
    have h15 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 120 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 113 7 h14 kg_2464_113
    have h16 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 220 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 120 100 h15 kg_2464_120
    have h17 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 290 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 220 70 h16 kg_2464_220
    have h18 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 297 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 290 7 h17 kg_2464_290
    have h19 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 299 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 297 2 h18 kg_2464_297
    have h20 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 317 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 299 18 h19 kg_2464_299
    have h21 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 319 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 317 2 h20 kg_2464_317
    have h22 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 350 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 319 31 h21 kg_2464_319
    have h23 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 380 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 350 30 h22 kg_2464_350
    have h24 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 401 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 380 21 h23 kg_2464_380
    have h25 : IPChk.allR (Pts.glueIB K2464.lits KW_2464) 0 427 = true := IPChk.allR_join (Pts.glueIB K2464.lits KW_2464) 0 401 26 h24 kg_2464_401
    exact h25
  have hlen : K2464.lits.length = 427 := by decide
  intro k h1 h2
  obtain rfl : k = 2464 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2464) K2464.lits KW_2464
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_436 : ∀ k, 2465 ≤ k → k < 2466 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2465 JW_2465 2465 1 jr_2465
theorem jr6_437 : ∀ k, 2466 ≤ k → k < 2467 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 409 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 2 = true := kb_2466_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 2 1 h0 kb_2466_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 3 8 h1 kb_2466_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 11 7 h2 kb_2466_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 18 1 h3 kb_2466_18
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 19 1 h4 kb_2466_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 20 8 h5 kb_2466_20
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 28 11 h6 kb_2466_28
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 39 19 h7 kb_2466_39
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 58 6 h8 kb_2466_58
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 64 2 h9 kb_2466_64
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 66 17 h10 kb_2466_66
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 83 6 h11 kb_2466_83
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 89 6 h12 kb_2466_89
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 95 10 h13 kb_2466_95
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 105 29 h14 kb_2466_105
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 134 2 h15 kb_2466_134
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 136 6 h16 kb_2466_136
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 142 50 h17 kb_2466_142
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 192 51 h18 kb_2466_192
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 243 39 h19 kb_2466_243
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 282 16 h20 kb_2466_282
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 298 1 h21 kb_2466_298
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 299 12 h22 kb_2466_299
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 311 1 h23 kb_2466_311
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 312 29 h24 kb_2466_312
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 341 22 h25 kb_2466_341
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 363 7 h26 kb_2466_363
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 370 1 h27 kb_2466_370
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 371 4 h28 kb_2466_371
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 375 1 h29 kb_2466_375
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 376 3 h30 kb_2466_376
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2466.lits.getD i 0)) 0 379 30 h31 kb_2466_379
    exact h32
  have hg : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 409 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 2 = true := kg_2466_0
    have h1 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 3 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 2 1 h0 kg_2466_2
    have h2 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 11 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 3 8 h1 kg_2466_3
    have h3 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 18 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 11 7 h2 kg_2466_11
    have h4 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 19 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 18 1 h3 kg_2466_18
    have h5 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 20 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 19 1 h4 kg_2466_19
    have h6 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 28 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 20 8 h5 kg_2466_20
    have h7 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 39 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 28 11 h6 kg_2466_28
    have h8 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 58 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 39 19 h7 kg_2466_39
    have h9 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 64 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 58 6 h8 kg_2466_58
    have h10 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 66 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 64 2 h9 kg_2466_64
    have h11 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 83 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 66 17 h10 kg_2466_66
    have h12 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 89 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 83 6 h11 kg_2466_83
    have h13 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 95 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 89 6 h12 kg_2466_89
    have h14 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 105 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 95 10 h13 kg_2466_95
    have h15 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 134 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 105 29 h14 kg_2466_105
    have h16 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 136 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 134 2 h15 kg_2466_134
    have h17 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 142 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 136 6 h16 kg_2466_136
    have h18 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 192 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 142 50 h17 kg_2466_142
    have h19 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 243 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 192 51 h18 kg_2466_192
    have h20 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 282 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 243 39 h19 kg_2466_243
    have h21 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 298 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 282 16 h20 kg_2466_282
    have h22 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 299 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 298 1 h21 kg_2466_298
    have h23 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 311 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 299 12 h22 kg_2466_299
    have h24 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 312 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 311 1 h23 kg_2466_311
    have h25 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 341 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 312 29 h24 kg_2466_312
    have h26 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 363 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 341 22 h25 kg_2466_341
    have h27 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 370 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 363 7 h26 kg_2466_363
    have h28 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 371 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 370 1 h27 kg_2466_370
    have h29 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 375 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 371 4 h28 kg_2466_371
    have h30 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 376 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 375 1 h29 kg_2466_375
    have h31 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 379 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 376 3 h30 kg_2466_376
    have h32 : IPChk.allR (Pts.glueIB K2466.lits KW_2466) 0 409 = true := IPChk.allR_join (Pts.glueIB K2466.lits KW_2466) 0 379 30 h31 kg_2466_379
    exact h32
  have hlen : K2466.lits.length = 409 := by decide
  intro k h1 h2
  obtain rfl : k = 2466 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2466) K2466.lits KW_2466
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_438 : ∀ k, 2467 ≤ k → k < 2469 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2467 JW_2467 2467 2 jr_2467
theorem jr6_439 : ∀ k, 2469 ≤ k → k < 2470 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 211 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 3 = true := kb_2469_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 3 16 h0 kb_2469_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 19 6 h1 kb_2469_19
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 25 5 h2 kb_2469_25
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 30 36 h3 kb_2469_30
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 66 20 h4 kb_2469_66
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 86 19 h5 kb_2469_86
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 105 1 h6 kb_2469_105
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 106 3 h7 kb_2469_106
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 109 1 h8 kb_2469_109
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 110 12 h9 kb_2469_110
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 122 49 h10 kb_2469_122
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 171 18 h11 kb_2469_171
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 189 7 h12 kb_2469_189
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 196 1 h13 kb_2469_196
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2469.lits.getD i 0)) 0 197 14 h14 kb_2469_197
    exact h15
  have hg : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 211 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 3 = true := kg_2469_0
    have h1 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 19 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 3 16 h0 kg_2469_3
    have h2 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 25 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 19 6 h1 kg_2469_19
    have h3 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 30 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 25 5 h2 kg_2469_25
    have h4 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 66 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 30 36 h3 kg_2469_30
    have h5 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 86 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 66 20 h4 kg_2469_66
    have h6 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 105 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 86 19 h5 kg_2469_86
    have h7 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 106 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 105 1 h6 kg_2469_105
    have h8 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 109 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 106 3 h7 kg_2469_106
    have h9 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 110 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 109 1 h8 kg_2469_109
    have h10 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 122 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 110 12 h9 kg_2469_110
    have h11 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 171 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 122 49 h10 kg_2469_122
    have h12 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 189 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 171 18 h11 kg_2469_171
    have h13 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 196 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 189 7 h12 kg_2469_189
    have h14 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 197 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 196 1 h13 kg_2469_196
    have h15 : IPChk.allR (Pts.glueIB K2469.lits KW_2469) 0 211 = true := IPChk.allR_join (Pts.glueIB K2469.lits KW_2469) 0 197 14 h14 kg_2469_197
    exact h15
  have hlen : K2469.lits.length = 211 := by decide
  intro k h1 h2
  obtain rfl : k = 2469 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2469) K2469.lits KW_2469
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_440 : ∀ k, 2470 ≤ k → k < 2471 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 261 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 2 = true := kb_2470_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 2 8 h0 kb_2470_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 10 7 h1 kb_2470_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 17 9 h2 kb_2470_17
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 26 21 h3 kb_2470_26
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 47 7 h4 kb_2470_47
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 54 2 h5 kb_2470_54
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 56 17 h6 kb_2470_56
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 73 6 h7 kb_2470_73
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 79 2 h8 kb_2470_79
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 81 15 h9 kb_2470_81
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 96 25 h10 kb_2470_96
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 121 26 h11 kb_2470_121
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 147 1 h12 kb_2470_147
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 148 16 h13 kb_2470_148
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 164 2 h14 kb_2470_164
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 166 31 h15 kb_2470_166
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 197 28 h16 kb_2470_197
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 225 3 h17 kb_2470_225
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 228 7 h18 kb_2470_228
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 235 12 h19 kb_2470_235
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2470.lits.getD i 0)) 0 247 14 h20 kb_2470_247
    exact h21
  have hg : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 261 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 2 = true := kg_2470_0
    have h1 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 10 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 2 8 h0 kg_2470_2
    have h2 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 17 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 10 7 h1 kg_2470_10
    have h3 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 26 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 17 9 h2 kg_2470_17
    have h4 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 47 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 26 21 h3 kg_2470_26
    have h5 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 54 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 47 7 h4 kg_2470_47
    have h6 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 56 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 54 2 h5 kg_2470_54
    have h7 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 73 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 56 17 h6 kg_2470_56
    have h8 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 79 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 73 6 h7 kg_2470_73
    have h9 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 81 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 79 2 h8 kg_2470_79
    have h10 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 96 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 81 15 h9 kg_2470_81
    have h11 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 121 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 96 25 h10 kg_2470_96
    have h12 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 147 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 121 26 h11 kg_2470_121
    have h13 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 148 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 147 1 h12 kg_2470_147
    have h14 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 164 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 148 16 h13 kg_2470_148
    have h15 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 166 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 164 2 h14 kg_2470_164
    have h16 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 197 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 166 31 h15 kg_2470_166
    have h17 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 225 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 197 28 h16 kg_2470_197
    have h18 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 228 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 225 3 h17 kg_2470_225
    have h19 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 235 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 228 7 h18 kg_2470_228
    have h20 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 247 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 235 12 h19 kg_2470_235
    have h21 : IPChk.allR (Pts.glueIB K2470.lits KW_2470) 0 261 = true := IPChk.allR_join (Pts.glueIB K2470.lits KW_2470) 0 247 14 h20 kg_2470_247
    exact h21
  have hlen : K2470.lits.length = 261 := by decide
  intro k h1 h2
  obtain rfl : k = 2470 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2470) K2470.lits KW_2470
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_441 : ∀ k, 2471 ≤ k → k < 2472 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2471 JW_2471 2471 1 jr_2471
theorem jr6_442 : ∀ k, 2472 ≤ k → k < 2473 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 115 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 1 = true := kb_2472_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 1 11 h0 kb_2472_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 12 56 h1 kb_2472_12
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2472.lits.getD i 0)) 0 68 47 h2 kb_2472_68
    exact h3
  have hg : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 115 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 1 = true := kg_2472_0
    have h1 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 12 = true := IPChk.allR_join (Pts.glueIB K2472.lits KW_2472) 0 1 11 h0 kg_2472_1
    have h2 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 68 = true := IPChk.allR_join (Pts.glueIB K2472.lits KW_2472) 0 12 56 h1 kg_2472_12
    have h3 : IPChk.allR (Pts.glueIB K2472.lits KW_2472) 0 115 = true := IPChk.allR_join (Pts.glueIB K2472.lits KW_2472) 0 68 47 h2 kg_2472_68
    exact h3
  have hlen : K2472.lits.length = 115 := by decide
  intro k h1 h2
  obtain rfl : k = 2472 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2472) K2472.lits KW_2472
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_443 : ∀ k, 2473 ≤ k → k < 2480 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2473 JW_2473 2473 7 jr_2473
theorem jr6_444 : ∀ k, 2480 ≤ k → k < 2481 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 72 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 2 = true := kb_2480_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 2 6 h0 kb_2480_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 8 3 h1 kb_2480_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 11 19 h2 kb_2480_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 30 14 h3 kb_2480_30
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 44 27 h4 kb_2480_44
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2480.lits.getD i 0)) 0 71 1 h5 kb_2480_71
    exact h6
  have hg : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 72 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 2 = true := kg_2480_0
    have h1 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 8 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 2 6 h0 kg_2480_2
    have h2 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 11 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 8 3 h1 kg_2480_8
    have h3 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 30 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 11 19 h2 kg_2480_11
    have h4 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 44 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 30 14 h3 kg_2480_30
    have h5 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 71 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 44 27 h4 kg_2480_44
    have h6 : IPChk.allR (Pts.glueIB K2480.lits KW_2480) 0 72 = true := IPChk.allR_join (Pts.glueIB K2480.lits KW_2480) 0 71 1 h5 kg_2480_71
    exact h6
  have hlen : K2480.lits.length = 72 := by decide
  intro k h1 h2
  obtain rfl : k = 2480 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2480) K2480.lits KW_2480
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_445 : ∀ k, 2481 ≤ k → k < 2503 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2481 JW_2481 2481 22 jr_2481
theorem jr6_446 : ∀ k, 2503 ≤ k → k < 2504 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2503.lits.getD i 0)) 0 2 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2503.lits.getD i 0)) 0 1 = true := kb_2503_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2503.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2503.lits.getD i 0)) 0 1 1 h0 kb_2503_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K2503.lits KW_2503) 0 2 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2503.lits KW_2503) 0 1 = true := kg_2503_0
    have h1 : IPChk.allR (Pts.glueIB K2503.lits KW_2503) 0 2 = true := IPChk.allR_join (Pts.glueIB K2503.lits KW_2503) 0 1 1 h0 kg_2503_1
    exact h1
  have hlen : K2503.lits.length = 2 := by decide
  intro k h1 h2
  obtain rfl : k = 2503 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2503) K2503.lits KW_2503
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_447 : ∀ k, 2504 ≤ k → k < 2510 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2504 JW_2504 2504 6 jr_2504
theorem jr6_448 : ∀ k, 2510 ≤ k → k < 2540 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2504 JW_2504 2510 30 jr_2510
theorem jr6_449 : ∀ k, 2540 ≤ k → k < 2549 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2504 JW_2504 2540 9 jr_2540
theorem jr6_450 : ∀ k, 2549 ≤ k → k < 2559 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2504 JW_2504 2549 10 jr_2549
theorem jr6_451 : ∀ k, 2559 ≤ k → k < 2560 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 249 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 4 = true := kb_2559_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 4 4 h0 kb_2559_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 8 7 h1 kb_2559_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 15 2 h2 kb_2559_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 17 15 h3 kb_2559_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 32 13 h4 kb_2559_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 45 5 h5 kb_2559_45
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 50 9 h6 kb_2559_50
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 59 25 h7 kb_2559_59
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 84 94 h8 kb_2559_84
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 178 13 h9 kb_2559_178
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 191 24 h10 kb_2559_191
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 215 30 h11 kb_2559_215
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 0 245 4 h12 kb_2559_245
    exact h13
  have hg : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 249 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 4 = true := kg_2559_0
    have h1 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 8 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 4 4 h0 kg_2559_4
    have h2 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 15 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 8 7 h1 kg_2559_8
    have h3 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 17 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 15 2 h2 kg_2559_15
    have h4 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 32 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 17 15 h3 kg_2559_17
    have h5 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 45 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 32 13 h4 kg_2559_32
    have h6 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 50 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 45 5 h5 kg_2559_45
    have h7 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 59 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 50 9 h6 kg_2559_50
    have h8 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 84 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 59 25 h7 kg_2559_59
    have h9 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 178 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 84 94 h8 kg_2559_84
    have h10 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 191 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 178 13 h9 kg_2559_178
    have h11 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 215 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 191 24 h10 kg_2559_191
    have h12 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 245 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 215 30 h11 kg_2559_215
    have h13 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 0 249 = true := IPChk.allR_join (Pts.glueIB K2559.lits KW_2559) 0 245 4 h12 kg_2559_245
    exact h13
  have hlen : K2559.lits.length = 249 := by decide
  intro k h1 h2
  obtain rfl : k = 2559 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2559) K2559.lits KW_2559
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_452 : ∀ k, 2560 ≤ k → k < 2561 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2560 JW_2560 2560 1 jr_2560
theorem jr6_453 : ∀ k, 2561 ≤ k → k < 2562 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 70 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 2 = true := kb_2561_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 2 13 h0 kb_2561_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 15 13 h1 kb_2561_15
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 28 23 h2 kb_2561_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2561.lits.getD i 0)) 0 51 19 h3 kb_2561_51
    exact h4
  have hg : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 70 = true := by
    have h0 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 2 = true := kg_2561_0
    have h1 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 15 = true := IPChk.allR_join (Pts.glueIB K2561.lits KW_2561) 0 2 13 h0 kg_2561_2
    have h2 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 28 = true := IPChk.allR_join (Pts.glueIB K2561.lits KW_2561) 0 15 13 h1 kg_2561_15
    have h3 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 51 = true := IPChk.allR_join (Pts.glueIB K2561.lits KW_2561) 0 28 23 h2 kg_2561_28
    have h4 : IPChk.allR (Pts.glueIB K2561.lits KW_2561) 0 70 = true := IPChk.allR_join (Pts.glueIB K2561.lits KW_2561) 0 51 19 h3 kg_2561_51
    exact h4
  have hlen : K2561.lits.length = 70 := by decide
  intro k h1 h2
  obtain rfl : k = 2561 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 2561) K2561.lits KW_2561
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_454 : ∀ k, 2562 ≤ k → k < 2564 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_2562 JW_2562 2562 2 jr_2562

theorem grp6_15 : ∀ k, 2456 ≤ k → k < 2564 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_428
  have a1 := Pts.fa_join a0 jr6_429
  have a2 := Pts.fa_join a1 jr6_430
  have a3 := Pts.fa_join a2 jr6_431
  have a4 := Pts.fa_join a3 jr6_432
  have a5 := Pts.fa_join a4 jr6_433
  have a6 := Pts.fa_join a5 jr6_434
  have a7 := Pts.fa_join a6 jr6_435
  have a8 := Pts.fa_join a7 jr6_436
  have a9 := Pts.fa_join a8 jr6_437
  have a10 := Pts.fa_join a9 jr6_438
  have a11 := Pts.fa_join a10 jr6_439
  have a12 := Pts.fa_join a11 jr6_440
  have a13 := Pts.fa_join a12 jr6_441
  have a14 := Pts.fa_join a13 jr6_442
  have a15 := Pts.fa_join a14 jr6_443
  have a16 := Pts.fa_join a15 jr6_444
  have a17 := Pts.fa_join a16 jr6_445
  have a18 := Pts.fa_join a17 jr6_446
  have a19 := Pts.fa_join a18 jr6_447
  have a20 := Pts.fa_join a19 jr6_448
  have a21 := Pts.fa_join a20 jr6_449
  have a22 := Pts.fa_join a21 jr6_450
  have a23 := Pts.fa_join a22 jr6_451
  have a24 := Pts.fa_join a23 jr6_452
  have a25 := Pts.fa_join a24 jr6_453
  have a26 := Pts.fa_join a25 jr6_454
  exact a26

end B334.E1x.Pts.S707
