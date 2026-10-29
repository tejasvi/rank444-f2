import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J299
import B334.E1x.Pts.S707.J301
import B334.E1x.Pts.S707.J305
import B334.E1x.Pts.S707.J307
import B334.E1x.Pts.S707.J315
import B334.E1x.Pts.S707.J365
import B334.E1x.Pts.S707.J367
import B334.E1x.Pts.S707.K298L
import B334.E1x.Pts.S707.K300L
import B334.E1x.Pts.S707.K303L
import B334.E1x.Pts.S707.K304L
import B334.E1x.Pts.S707.K306L
import B334.E1x.Pts.S707.K314L
import B334.E1x.Pts.S707.K363L
import B334.E1x.Pts.S707.K364L
import B334.E1x.Pts.S707.K366L
import B334.E1x.Pts.S707.K298C0
import B334.E1x.Pts.S707.K298C1
import B334.E1x.Pts.S707.K298C2
import B334.E1x.Pts.S707.K298C3
import B334.E1x.Pts.S707.K298C4
import B334.E1x.Pts.S707.K298C5
import B334.E1x.Pts.S707.K298C6
import B334.E1x.Pts.S707.K300Q0
import B334.E1x.Pts.S707.K300Q1
import B334.E1x.Pts.S707.K300Q2
import B334.E1x.Pts.S707.K300Q3
import B334.E1x.Pts.S707.K300Q4
import B334.E1x.Pts.S707.K300Q5
import B334.E1x.Pts.S707.K300Q6
import B334.E1x.Pts.S707.K303Q0
import B334.E1x.Pts.S707.K303Q1
import B334.E1x.Pts.S707.K303Q2
import B334.E1x.Pts.S707.K303Q3
import B334.E1x.Pts.S707.K303Q4
import B334.E1x.Pts.S707.K303Q5
import B334.E1x.Pts.S707.K303Q6
import B334.E1x.Pts.S707.K303Q7
import B334.E1x.Pts.S707.K303Q8
import B334.E1x.Pts.S707.K303Q9
import B334.E1x.Pts.S707.K304Q0
import B334.E1x.Pts.S707.K304Q1
import B334.E1x.Pts.S707.K304Q2
import B334.E1x.Pts.S707.K304Q3
import B334.E1x.Pts.S707.K304Q4
import B334.E1x.Pts.S707.K304Q5
import B334.E1x.Pts.S707.K304Q6
import B334.E1x.Pts.S707.K304Q7
import B334.E1x.Pts.S707.K304Q8
import B334.E1x.Pts.S707.K304Q9
import B334.E1x.Pts.S707.K306Q0
import B334.E1x.Pts.S707.K306Q1
import B334.E1x.Pts.S707.K306Q2
import B334.E1x.Pts.S707.K306Q3
import B334.E1x.Pts.S707.K306Q4
import B334.E1x.Pts.S707.K306Q5
import B334.E1x.Pts.S707.K306Q6
import B334.E1x.Pts.S707.K306Q7
import B334.E1x.Pts.S707.K306Q8
import B334.E1x.Pts.S707.K314Q0
import B334.E1x.Pts.S707.K314Q1
import B334.E1x.Pts.S707.K314Q2
import B334.E1x.Pts.S707.K363C0
import B334.E1x.Pts.S707.K363C1
import B334.E1x.Pts.S707.K363C2
import B334.E1x.Pts.S707.K363C3
import B334.E1x.Pts.S707.K364C0
import B334.E1x.Pts.S707.K366Q0
import B334.E1x.Pts.S707.K366Q1
import B334.E1x.Pts.S707.K366Q2
import B334.E1x.Pts.S707.K366Q3
import B334.E1x.Pts.S707.K366Q4
import B334.E1x.Pts.S707.K366Q5
import B334.E1x.Pts.S707.K303Q10
import B334.E1x.Pts.S707.K304Q10

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 298 … 392 (stage707_v6): the v5 Fin's job blocks r71 … r87 as
theorems, joined into `grp6_3` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_71 : ∀ k, 298 ≤ k → k < 299 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2223 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 6 = true := kb_298_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 6 4 h0 kb_298_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 10 24 h1 kb_298_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 34 9 h2 kb_298_34
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 43 5 h3 kb_298_43
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 48 15 h4 kb_298_48
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 63 8 h5 kb_298_63
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 71 10 h6 kb_298_71
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 81 2 h7 kb_298_81
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 83 29 h8 kb_298_83
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 112 2 h9 kb_298_112
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 114 6 h10 kb_298_114
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 120 2 h11 kb_298_120
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 122 27 h12 kb_298_122
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 149 6 h13 kb_298_149
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 155 2 h14 kb_298_155
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 157 23 h15 kb_298_157
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 180 2 h16 kb_298_180
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 182 33 h17 kb_298_182
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 215 23 h18 kb_298_215
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 238 8 h19 kb_298_238
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 246 8 h20 kb_298_246
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 254 2 h21 kb_298_254
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 256 29 h22 kb_298_256
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 285 28 h23 kb_298_285
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 313 16 h24 kb_298_313
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 329 15 h25 kb_298_329
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 344 14 h26 kb_298_344
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 358 30 h27 kb_298_358
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 388 16 h28 kb_298_388
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 404 6 h29 kb_298_404
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 410 22 h30 kb_298_410
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 432 12 h31 kb_298_432
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 444 4 h32 kb_298_444
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 477 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 448 29 h33 kb_298_448
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 477 26 h34 kb_298_477
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 503 16 h35 kb_298_503
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 519 6 h36 kb_298_519
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 525 2 h37 kb_298_525
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 527 27 h38 kb_298_527
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 554 2 h39 kb_298_554
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 556 23 h40 kb_298_556
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 579 31 h41 kb_298_579
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 610 50 h42 kb_298_610
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 669 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 660 9 h43 kb_298_660
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 669 1 h44 kb_298_669
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 670 12 h45 kb_298_670
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 705 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 682 23 h46 kb_298_682
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 736 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 705 31 h47 kb_298_705
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 738 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 736 2 h48 kb_298_736
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 752 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 738 14 h49 kb_298_738
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 754 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 752 2 h50 kb_298_752
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 754 24 h51 kb_298_754
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 780 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 778 2 h52 kb_298_778
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 780 6 h53 kb_298_780
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 788 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 786 2 h54 kb_298_786
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 807 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 788 19 h55 kb_298_788
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 807 11 h56 kb_298_807
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 818 12 h57 kb_298_818
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 830 12 h58 kb_298_830
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 842 27 h59 kb_298_842
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 897 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 869 28 h60 kb_298_869
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 897 2 h61 kb_298_897
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 917 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 899 18 h62 kb_298_899
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 941 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 917 24 h63 kb_298_917
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 941 24 h64 kb_298_941
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 980 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 965 15 h65 kb_298_965
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1033 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 980 53 h66 kb_298_980
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1035 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1033 2 h67 kb_298_1033
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1051 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1035 16 h68 kb_298_1035
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1051 54 h69 kb_298_1051
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1105 44 h70 kb_298_1105
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1149 11 h71 kb_298_1149
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1160 2 h72 kb_298_1160
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1162 34 h73 kb_298_1162
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1196 15 h74 kb_298_1196
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1211 2 h75 kb_298_1211
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1213 21 h76 kb_298_1213
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1234 30 h77 kb_298_1234
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1264 3 h78 kb_298_1264
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1267 30 h79 kb_298_1267
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1297 31 h80 kb_298_1297
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1328 52 h81 kb_298_1328
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1380 7 h82 kb_298_1380
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1387 58 h83 kb_298_1387
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1445 36 h84 kb_298_1445
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1481 1 h85 kb_298_1481
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1482 12 h86 kb_298_1482
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1494 20 h87 kb_298_1494
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1514 20 h88 kb_298_1514
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1534 12 h89 kb_298_1534
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1546 6 h90 kb_298_1546
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1552 1 h91 kb_298_1552
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1553 13 h92 kb_298_1553
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1566 1 h93 kb_298_1566
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1567 9 h94 kb_298_1567
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1593 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1576 17 h95 kb_298_1576
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1604 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1593 11 h96 kb_298_1593
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1659 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1604 55 h97 kb_298_1604
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1659 6 h98 kb_298_1659
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1665 15 h99 kb_298_1665
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1680 46 h100 kb_298_1680
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1755 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1726 29 h101 kb_298_1726
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1761 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1755 6 h102 kb_298_1755
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1790 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1761 29 h103 kb_298_1761
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1825 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1790 35 h104 kb_298_1790
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1861 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1825 36 h105 kb_298_1825
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1861 1 h106 kb_298_1861
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1894 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1862 32 h107 kb_298_1862
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1904 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1894 10 h108 kb_298_1894
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1904 31 h109 kb_298_1904
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1935 28 h110 kb_298_1935
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1963 26 h111 kb_298_1963
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1989 5 h112 kb_298_1989
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2000 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 1994 6 h113 kb_298_1994
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2064 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2000 64 h114 kb_298_2000
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2089 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2064 25 h115 kb_298_2064
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2096 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2089 7 h116 kb_298_2089
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2096 5 h117 kb_298_2096
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2101 1 h118 kb_298_2101
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2102 12 h119 kb_298_2102
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2114 1 h120 kb_298_2114
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2115 4 h121 kb_298_2115
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2119 7 h122 kb_298_2119
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2126 18 h123 kb_298_2126
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2144 1 h124 kb_298_2144
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2145 27 h125 kb_298_2145
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2172 1 h126 kb_298_2172
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2173 32 h127 kb_298_2173
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2205 13 h128 kb_298_2205
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2218 2 h129 kb_298_2218
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K298.lits.getD i 0)) 0 2220 3 h130 kb_298_2220
    exact h131
  have hg : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2223 = true := by
    have h0 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 6 = true := kg_298_0
    have h1 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 10 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 6 4 h0 kg_298_6
    have h2 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 34 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 10 24 h1 kg_298_10
    have h3 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 43 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 34 9 h2 kg_298_34
    have h4 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 48 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 43 5 h3 kg_298_43
    have h5 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 63 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 48 15 h4 kg_298_48
    have h6 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 71 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 63 8 h5 kg_298_63
    have h7 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 81 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 71 10 h6 kg_298_71
    have h8 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 83 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 81 2 h7 kg_298_81
    have h9 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 112 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 83 29 h8 kg_298_83
    have h10 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 114 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 112 2 h9 kg_298_112
    have h11 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 120 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 114 6 h10 kg_298_114
    have h12 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 122 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 120 2 h11 kg_298_120
    have h13 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 149 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 122 27 h12 kg_298_122
    have h14 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 155 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 149 6 h13 kg_298_149
    have h15 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 157 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 155 2 h14 kg_298_155
    have h16 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 180 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 157 23 h15 kg_298_157
    have h17 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 182 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 180 2 h16 kg_298_180
    have h18 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 215 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 182 33 h17 kg_298_182
    have h19 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 238 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 215 23 h18 kg_298_215
    have h20 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 246 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 238 8 h19 kg_298_238
    have h21 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 254 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 246 8 h20 kg_298_246
    have h22 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 256 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 254 2 h21 kg_298_254
    have h23 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 285 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 256 29 h22 kg_298_256
    have h24 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 313 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 285 28 h23 kg_298_285
    have h25 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 329 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 313 16 h24 kg_298_313
    have h26 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 344 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 329 15 h25 kg_298_329
    have h27 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 358 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 344 14 h26 kg_298_344
    have h28 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 388 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 358 30 h27 kg_298_358
    have h29 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 404 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 388 16 h28 kg_298_388
    have h30 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 410 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 404 6 h29 kg_298_404
    have h31 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 432 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 410 22 h30 kg_298_410
    have h32 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 444 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 432 12 h31 kg_298_432
    have h33 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 448 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 444 4 h32 kg_298_444
    have h34 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 477 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 448 29 h33 kg_298_448
    have h35 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 503 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 477 26 h34 kg_298_477
    have h36 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 519 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 503 16 h35 kg_298_503
    have h37 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 525 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 519 6 h36 kg_298_519
    have h38 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 527 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 525 2 h37 kg_298_525
    have h39 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 554 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 527 27 h38 kg_298_527
    have h40 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 556 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 554 2 h39 kg_298_554
    have h41 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 579 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 556 23 h40 kg_298_556
    have h42 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 610 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 579 31 h41 kg_298_579
    have h43 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 660 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 610 50 h42 kg_298_610
    have h44 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 669 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 660 9 h43 kg_298_660
    have h45 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 670 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 669 1 h44 kg_298_669
    have h46 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 682 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 670 12 h45 kg_298_670
    have h47 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 705 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 682 23 h46 kg_298_682
    have h48 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 736 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 705 31 h47 kg_298_705
    have h49 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 738 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 736 2 h48 kg_298_736
    have h50 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 752 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 738 14 h49 kg_298_738
    have h51 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 754 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 752 2 h50 kg_298_752
    have h52 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 778 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 754 24 h51 kg_298_754
    have h53 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 780 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 778 2 h52 kg_298_778
    have h54 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 786 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 780 6 h53 kg_298_780
    have h55 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 788 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 786 2 h54 kg_298_786
    have h56 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 807 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 788 19 h55 kg_298_788
    have h57 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 818 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 807 11 h56 kg_298_807
    have h58 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 830 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 818 12 h57 kg_298_818
    have h59 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 842 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 830 12 h58 kg_298_830
    have h60 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 869 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 842 27 h59 kg_298_842
    have h61 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 897 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 869 28 h60 kg_298_869
    have h62 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 899 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 897 2 h61 kg_298_897
    have h63 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 917 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 899 18 h62 kg_298_899
    have h64 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 941 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 917 24 h63 kg_298_917
    have h65 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 965 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 941 24 h64 kg_298_941
    have h66 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 980 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 965 15 h65 kg_298_965
    have h67 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1033 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 980 53 h66 kg_298_980
    have h68 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1035 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1033 2 h67 kg_298_1033
    have h69 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1051 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1035 16 h68 kg_298_1035
    have h70 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1105 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1051 54 h69 kg_298_1051
    have h71 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1149 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1105 44 h70 kg_298_1105
    have h72 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1160 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1149 11 h71 kg_298_1149
    have h73 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1162 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1160 2 h72 kg_298_1160
    have h74 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1196 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1162 34 h73 kg_298_1162
    have h75 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1211 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1196 15 h74 kg_298_1196
    have h76 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1213 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1211 2 h75 kg_298_1211
    have h77 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1234 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1213 21 h76 kg_298_1213
    have h78 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1264 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1234 30 h77 kg_298_1234
    have h79 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1267 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1264 3 h78 kg_298_1264
    have h80 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1297 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1267 30 h79 kg_298_1267
    have h81 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1328 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1297 31 h80 kg_298_1297
    have h82 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1380 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1328 52 h81 kg_298_1328
    have h83 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1387 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1380 7 h82 kg_298_1380
    have h84 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1445 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1387 58 h83 kg_298_1387
    have h85 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1481 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1445 36 h84 kg_298_1445
    have h86 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1482 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1481 1 h85 kg_298_1481
    have h87 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1494 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1482 12 h86 kg_298_1482
    have h88 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1514 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1494 20 h87 kg_298_1494
    have h89 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1534 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1514 20 h88 kg_298_1514
    have h90 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1546 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1534 12 h89 kg_298_1534
    have h91 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1552 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1546 6 h90 kg_298_1546
    have h92 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1553 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1552 1 h91 kg_298_1552
    have h93 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1566 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1553 13 h92 kg_298_1553
    have h94 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1567 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1566 1 h93 kg_298_1566
    have h95 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1576 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1567 9 h94 kg_298_1567
    have h96 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1593 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1576 17 h95 kg_298_1576
    have h97 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1604 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1593 11 h96 kg_298_1593
    have h98 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1659 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1604 55 h97 kg_298_1604
    have h99 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1665 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1659 6 h98 kg_298_1659
    have h100 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1680 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1665 15 h99 kg_298_1665
    have h101 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1726 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1680 46 h100 kg_298_1680
    have h102 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1755 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1726 29 h101 kg_298_1726
    have h103 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1761 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1755 6 h102 kg_298_1755
    have h104 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1790 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1761 29 h103 kg_298_1761
    have h105 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1825 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1790 35 h104 kg_298_1790
    have h106 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1861 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1825 36 h105 kg_298_1825
    have h107 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1862 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1861 1 h106 kg_298_1861
    have h108 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1894 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1862 32 h107 kg_298_1862
    have h109 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1904 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1894 10 h108 kg_298_1894
    have h110 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1935 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1904 31 h109 kg_298_1904
    have h111 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1963 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1935 28 h110 kg_298_1935
    have h112 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1989 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1963 26 h111 kg_298_1963
    have h113 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 1994 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1989 5 h112 kg_298_1989
    have h114 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2000 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 1994 6 h113 kg_298_1994
    have h115 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2064 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2000 64 h114 kg_298_2000
    have h116 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2089 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2064 25 h115 kg_298_2064
    have h117 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2096 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2089 7 h116 kg_298_2089
    have h118 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2101 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2096 5 h117 kg_298_2096
    have h119 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2102 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2101 1 h118 kg_298_2101
    have h120 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2114 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2102 12 h119 kg_298_2102
    have h121 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2115 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2114 1 h120 kg_298_2114
    have h122 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2119 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2115 4 h121 kg_298_2115
    have h123 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2126 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2119 7 h122 kg_298_2119
    have h124 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2144 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2126 18 h123 kg_298_2126
    have h125 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2145 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2144 1 h124 kg_298_2144
    have h126 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2172 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2145 27 h125 kg_298_2145
    have h127 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2173 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2172 1 h126 kg_298_2172
    have h128 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2205 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2173 32 h127 kg_298_2173
    have h129 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2218 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2205 13 h128 kg_298_2205
    have h130 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2220 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2218 2 h129 kg_298_2218
    have h131 : IPChk.allR (Pts.glueIB K298.lits KW_298) 0 2223 = true := IPChk.allR_join (Pts.glueIB K298.lits KW_298) 0 2220 3 h130 kg_298_2220
    exact h131
  have hlen : K298.lits.length = 2223 := by decide
  intro k h1 h2
  obtain rfl : k = 298 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 298) K298.lits KW_298
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_72 : ∀ k, 299 ≤ k → k < 300 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_299 JW_299 299 1 jr_299
theorem jr6_73 : ∀ k, 300 ≤ k → k < 301 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 852 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 3 = true := kb_300_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 3 4 h0 kb_300_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 7 5 h1 kb_300_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 12 5 h2 kb_300_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 17 8 h3 kb_300_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 25 2 h4 kb_300_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 27 1 h5 kb_300_27
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 28 26 h6 kb_300_28
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 54 5 h7 kb_300_54
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 59 7 h8 kb_300_59
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 66 19 h9 kb_300_66
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 85 6 h10 kb_300_85
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 91 6 h11 kb_300_91
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 97 1 h12 kb_300_97
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 98 45 h13 kb_300_98
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 143 7 h14 kb_300_143
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 150 2 h15 kb_300_150
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 152 31 h16 kb_300_152
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 183 20 h17 kb_300_183
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 203 11 h18 kb_300_203
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 214 8 h19 kb_300_214
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 222 12 h20 kb_300_222
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 234 15 h21 kb_300_234
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 249 2 h22 kb_300_249
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 251 23 h23 kb_300_251
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 274 7 h24 kb_300_274
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 295 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 281 14 h25 kb_300_281
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 295 1 h26 kb_300_295
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 296 2 h27 kb_300_296
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 298 2 h28 kb_300_298
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 300 1 h29 kb_300_300
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 301 2 h30 kb_300_301
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 303 2 h31 kb_300_303
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 305 2 h32 kb_300_305
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 307 1 h33 kb_300_307
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 308 1 h34 kb_300_308
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 309 2 h35 kb_300_309
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 311 2 h36 kb_300_311
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 313 2 h37 kb_300_313
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 315 3 h38 kb_300_315
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 318 58 h39 kb_300_318
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 376 13 h40 kb_300_376
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 389 29 h41 kb_300_389
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 418 2 h42 kb_300_418
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 426 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 420 6 h43 kb_300_420
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 426 23 h44 kb_300_426
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 449 6 h45 kb_300_449
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 477 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 455 22 h46 kb_300_455
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 477 30 h47 kb_300_477
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 507 44 h48 kb_300_507
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 551 14 h49 kb_300_551
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 565 7 h50 kb_300_565
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 574 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 572 2 h51 kb_300_572
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 574 2 h52 kb_300_574
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 576 6 h53 kb_300_576
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 582 20 h54 kb_300_582
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 604 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 602 2 h55 kb_300_602
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 605 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 604 1 h56 kb_300_604
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 605 1 h57 kb_300_605
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 608 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 606 2 h58 kb_300_606
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 608 26 h59 kb_300_608
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 724 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 634 90 h60 kb_300_634
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 754 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 724 30 h61 kb_300_724
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 817 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 754 63 h62 kb_300_754
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 817 17 h63 kb_300_817
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 852 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 834 18 h64 kb_300_834
    exact h65
  have hg : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 852 = true := by
    have h0 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 3 = true := kg_300_0
    have h1 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 7 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 3 4 h0 kg_300_3
    have h2 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 12 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 7 5 h1 kg_300_7
    have h3 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 17 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 12 5 h2 kg_300_12
    have h4 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 25 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 17 8 h3 kg_300_17
    have h5 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 27 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 25 2 h4 kg_300_25
    have h6 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 28 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 27 1 h5 kg_300_27
    have h7 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 54 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 28 26 h6 kg_300_28
    have h8 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 59 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 54 5 h7 kg_300_54
    have h9 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 66 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 59 7 h8 kg_300_59
    have h10 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 85 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 66 19 h9 kg_300_66
    have h11 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 91 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 85 6 h10 kg_300_85
    have h12 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 97 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 91 6 h11 kg_300_91
    have h13 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 98 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 97 1 h12 kg_300_97
    have h14 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 143 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 98 45 h13 kg_300_98
    have h15 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 150 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 143 7 h14 kg_300_143
    have h16 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 152 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 150 2 h15 kg_300_150
    have h17 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 183 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 152 31 h16 kg_300_152
    have h18 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 203 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 183 20 h17 kg_300_183
    have h19 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 214 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 203 11 h18 kg_300_203
    have h20 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 222 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 214 8 h19 kg_300_214
    have h21 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 234 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 222 12 h20 kg_300_222
    have h22 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 249 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 234 15 h21 kg_300_234
    have h23 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 251 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 249 2 h22 kg_300_249
    have h24 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 274 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 251 23 h23 kg_300_251
    have h25 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 281 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 274 7 h24 kg_300_274
    have h26 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 295 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 281 14 h25 kg_300_281
    have h27 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 296 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 295 1 h26 kg_300_295
    have h28 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 298 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 296 2 h27 kg_300_296
    have h29 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 300 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 298 2 h28 kg_300_298
    have h30 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 301 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 300 1 h29 kg_300_300
    have h31 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 303 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 301 2 h30 kg_300_301
    have h32 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 305 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 303 2 h31 kg_300_303
    have h33 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 307 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 305 2 h32 kg_300_305
    have h34 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 308 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 307 1 h33 kg_300_307
    have h35 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 309 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 308 1 h34 kg_300_308
    have h36 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 311 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 309 2 h35 kg_300_309
    have h37 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 313 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 311 2 h36 kg_300_311
    have h38 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 315 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 313 2 h37 kg_300_313
    have h39 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 318 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 315 3 h38 kg_300_315
    have h40 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 376 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 318 58 h39 kg_300_318
    have h41 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 389 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 376 13 h40 kg_300_376
    have h42 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 418 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 389 29 h41 kg_300_389
    have h43 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 420 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 418 2 h42 kg_300_418
    have h44 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 426 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 420 6 h43 kg_300_420
    have h45 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 449 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 426 23 h44 kg_300_426
    have h46 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 455 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 449 6 h45 kg_300_449
    have h47 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 477 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 455 22 h46 kg_300_455
    have h48 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 507 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 477 30 h47 kg_300_477
    have h49 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 551 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 507 44 h48 kg_300_507
    have h50 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 565 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 551 14 h49 kg_300_551
    have h51 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 572 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 565 7 h50 kg_300_565
    have h52 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 574 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 572 2 h51 kg_300_572
    have h53 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 576 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 574 2 h52 kg_300_574
    have h54 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 582 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 576 6 h53 kg_300_576
    have h55 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 602 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 582 20 h54 kg_300_582
    have h56 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 604 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 602 2 h55 kg_300_602
    have h57 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 605 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 604 1 h56 kg_300_604
    have h58 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 606 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 605 1 h57 kg_300_605
    have h59 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 608 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 606 2 h58 kg_300_606
    have h60 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 634 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 608 26 h59 kg_300_608
    have h61 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 724 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 634 90 h60 kg_300_634
    have h62 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 754 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 724 30 h61 kg_300_724
    have h63 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 817 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 754 63 h62 kg_300_754
    have h64 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 834 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 817 17 h63 kg_300_817
    have h65 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 852 = true := IPChk.allR_join (Pts.glueIB K300.lits KW_300) 0 834 18 h64 kg_300_834
    exact h65
  have hlen : K300.lits.length = 852 := by decide
  intro k h1 h2
  obtain rfl : k = 300 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 300) K300.lits KW_300
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_74 : ∀ k, 301 ≤ k → k < 303 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_301 JW_301 301 2 jr_301
theorem jr6_75 : ∀ k, 303 ≤ k → k < 304 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1528 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 3 = true := kb_303_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 3 8 h0 kb_303_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 11 13 h1 kb_303_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 24 12 h2 kb_303_24
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 36 6 h3 kb_303_36
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 42 29 h4 kb_303_42
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 71 2 h5 kb_303_71
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 73 6 h6 kb_303_73
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 79 2 h7 kb_303_79
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 81 26 h8 kb_303_81
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 107 6 h9 kb_303_107
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 113 2 h10 kb_303_113
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 115 14 h11 kb_303_115
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 129 11 h12 kb_303_129
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 140 29 h13 kb_303_140
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 169 2 h14 kb_303_169
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 171 6 h15 kb_303_171
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 177 2 h16 kb_303_177
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 179 22 h17 kb_303_179
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 201 13 h18 kb_303_201
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 214 24 h19 kb_303_214
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 238 35 h20 kb_303_238
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 273 2 h21 kb_303_273
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 275 15 h22 kb_303_275
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 290 6 h23 kb_303_290
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 296 2 h24 kb_303_296
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 325 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 298 27 h25 kb_303_298
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 325 2 h26 kb_303_325
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 327 23 h27 kb_303_327
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 350 30 h28 kb_303_350
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 380 49 h29 kb_303_380
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 429 9 h30 kb_303_429
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 438 13 h31 kb_303_438
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 451 6 h32 kb_303_451
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 457 15 h33 kb_303_457
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 472 13 h34 kb_303_472
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 501 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 485 16 h35 kb_303_485
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 501 13 h36 kb_303_501
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 514 15 h37 kb_303_514
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 529 6 h38 kb_303_529
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 535 2 h39 kb_303_535
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 537 14 h40 kb_303_537
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 551 8 h41 kb_303_551
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 559 2 h42 kb_303_559
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 568 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 561 7 h43 kb_303_561
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 581 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 568 13 h44 kb_303_568
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 581 10 h45 kb_303_581
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 591 19 h46 kb_303_591
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 610 2 h47 kb_303_610
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 612 14 h48 kb_303_612
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 626 8 h49 kb_303_626
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 634 8 h50 kb_303_634
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 642 51 h51 kb_303_642
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 693 4 h52 kb_303_693
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 697 2 h53 kb_303_697
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 699 23 h54 kb_303_699
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 728 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 722 6 h55 kb_303_722
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 728 2 h56 kb_303_728
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 730 26 h57 kb_303_730
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 756 19 h58 kb_303_756
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 775 8 h59 kb_303_775
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 783 19 h60 kb_303_783
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 831 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 802 29 h61 kb_303_802
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 831 31 h62 kb_303_831
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 908 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 862 46 h63 kb_303_862
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 908 19 h64 kb_303_908
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 933 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 927 6 h65 kb_303_927
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 933 2 h66 kb_303_933
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 935 19 h67 kb_303_935
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 954 4 h68 kb_303_954
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 960 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 958 2 h69 kb_303_958
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 960 18 h70 kb_303_960
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 999 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 978 21 h71 kb_303_978
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1012 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 999 13 h72 kb_303_999
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1012 31 h73 kb_303_1012
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1051 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1043 8 h74 kb_303_1043
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1054 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1051 3 h75 kb_303_1051
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1070 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1054 16 h76 kb_303_1054
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1077 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1070 7 h77 kb_303_1070
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1089 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1077 12 h78 kb_303_1077
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1090 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1089 1 h79 kb_303_1089
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1090 7 h80 kb_303_1090
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1099 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1097 2 h81 kb_303_1097
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1099 15 h82 kb_303_1099
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1114 15 h83 kb_303_1114
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1129 15 h84 kb_303_1129
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1144 2 h85 kb_303_1144
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1146 4 h86 kb_303_1146
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1150 12 h87 kb_303_1150
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1162 1 h88 kb_303_1162
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1163 2 h89 kb_303_1163
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1165 42 h90 kb_303_1165
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1207 49 h91 kb_303_1207
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1256 1 h92 kb_303_1256
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1257 31 h93 kb_303_1257
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1288 11 h94 kb_303_1288
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1299 32 h95 kb_303_1299
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1331 32 h96 kb_303_1331
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1363 13 h97 kb_303_1363
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1376 1 h98 kb_303_1376
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1377 31 h99 kb_303_1377
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1408 7 h100 kb_303_1408
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1415 18 h101 kb_303_1415
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1433 14 h102 kb_303_1433
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1447 1 h103 kb_303_1447
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1448 17 h104 kb_303_1448
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1465 9 h105 kb_303_1465
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1474 5 h106 kb_303_1474
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1479 3 h107 kb_303_1479
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1528 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 1482 46 h108 kb_303_1482
    exact h109
  have hg : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1528 = true := by
    have h0 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 3 = true := kg_303_0
    have h1 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 11 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 3 8 h0 kg_303_3
    have h2 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 24 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 11 13 h1 kg_303_11
    have h3 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 36 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 24 12 h2 kg_303_24
    have h4 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 42 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 36 6 h3 kg_303_36
    have h5 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 71 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 42 29 h4 kg_303_42
    have h6 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 73 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 71 2 h5 kg_303_71
    have h7 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 79 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 73 6 h6 kg_303_73
    have h8 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 81 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 79 2 h7 kg_303_79
    have h9 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 107 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 81 26 h8 kg_303_81
    have h10 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 113 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 107 6 h9 kg_303_107
    have h11 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 115 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 113 2 h10 kg_303_113
    have h12 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 129 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 115 14 h11 kg_303_115
    have h13 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 140 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 129 11 h12 kg_303_129
    have h14 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 169 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 140 29 h13 kg_303_140
    have h15 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 171 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 169 2 h14 kg_303_169
    have h16 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 177 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 171 6 h15 kg_303_171
    have h17 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 179 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 177 2 h16 kg_303_177
    have h18 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 201 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 179 22 h17 kg_303_179
    have h19 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 214 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 201 13 h18 kg_303_201
    have h20 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 238 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 214 24 h19 kg_303_214
    have h21 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 273 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 238 35 h20 kg_303_238
    have h22 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 275 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 273 2 h21 kg_303_273
    have h23 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 290 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 275 15 h22 kg_303_275
    have h24 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 296 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 290 6 h23 kg_303_290
    have h25 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 298 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 296 2 h24 kg_303_296
    have h26 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 325 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 298 27 h25 kg_303_298
    have h27 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 327 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 325 2 h26 kg_303_325
    have h28 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 350 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 327 23 h27 kg_303_327
    have h29 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 380 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 350 30 h28 kg_303_350
    have h30 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 429 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 380 49 h29 kg_303_380
    have h31 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 438 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 429 9 h30 kg_303_429
    have h32 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 451 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 438 13 h31 kg_303_438
    have h33 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 457 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 451 6 h32 kg_303_451
    have h34 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 472 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 457 15 h33 kg_303_457
    have h35 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 485 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 472 13 h34 kg_303_472
    have h36 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 501 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 485 16 h35 kg_303_485
    have h37 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 514 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 501 13 h36 kg_303_501
    have h38 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 529 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 514 15 h37 kg_303_514
    have h39 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 535 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 529 6 h38 kg_303_529
    have h40 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 537 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 535 2 h39 kg_303_535
    have h41 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 551 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 537 14 h40 kg_303_537
    have h42 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 559 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 551 8 h41 kg_303_551
    have h43 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 561 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 559 2 h42 kg_303_559
    have h44 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 568 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 561 7 h43 kg_303_561
    have h45 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 581 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 568 13 h44 kg_303_568
    have h46 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 591 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 581 10 h45 kg_303_581
    have h47 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 610 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 591 19 h46 kg_303_591
    have h48 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 612 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 610 2 h47 kg_303_610
    have h49 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 626 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 612 14 h48 kg_303_612
    have h50 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 634 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 626 8 h49 kg_303_626
    have h51 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 642 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 634 8 h50 kg_303_634
    have h52 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 693 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 642 51 h51 kg_303_642
    have h53 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 697 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 693 4 h52 kg_303_693
    have h54 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 699 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 697 2 h53 kg_303_697
    have h55 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 722 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 699 23 h54 kg_303_699
    have h56 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 728 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 722 6 h55 kg_303_722
    have h57 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 730 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 728 2 h56 kg_303_728
    have h58 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 756 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 730 26 h57 kg_303_730
    have h59 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 775 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 756 19 h58 kg_303_756
    have h60 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 783 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 775 8 h59 kg_303_775
    have h61 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 802 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 783 19 h60 kg_303_783
    have h62 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 831 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 802 29 h61 kg_303_802
    have h63 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 862 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 831 31 h62 kg_303_831
    have h64 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 908 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 862 46 h63 kg_303_862
    have h65 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 927 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 908 19 h64 kg_303_908
    have h66 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 933 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 927 6 h65 kg_303_927
    have h67 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 935 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 933 2 h66 kg_303_933
    have h68 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 954 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 935 19 h67 kg_303_935
    have h69 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 958 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 954 4 h68 kg_303_954
    have h70 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 960 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 958 2 h69 kg_303_958
    have h71 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 978 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 960 18 h70 kg_303_960
    have h72 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 999 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 978 21 h71 kg_303_978
    have h73 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1012 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 999 13 h72 kg_303_999
    have h74 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1043 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1012 31 h73 kg_303_1012
    have h75 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1051 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1043 8 h74 kg_303_1043
    have h76 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1054 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1051 3 h75 kg_303_1051
    have h77 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1070 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1054 16 h76 kg_303_1054
    have h78 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1077 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1070 7 h77 kg_303_1070
    have h79 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1089 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1077 12 h78 kg_303_1077
    have h80 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1090 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1089 1 h79 kg_303_1089
    have h81 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1097 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1090 7 h80 kg_303_1090
    have h82 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1099 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1097 2 h81 kg_303_1097
    have h83 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1114 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1099 15 h82 kg_303_1099
    have h84 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1129 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1114 15 h83 kg_303_1114
    have h85 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1144 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1129 15 h84 kg_303_1129
    have h86 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1146 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1144 2 h85 kg_303_1144
    have h87 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1150 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1146 4 h86 kg_303_1146
    have h88 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1162 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1150 12 h87 kg_303_1150
    have h89 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1163 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1162 1 h88 kg_303_1162
    have h90 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1165 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1163 2 h89 kg_303_1163
    have h91 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1207 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1165 42 h90 kg_303_1165
    have h92 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1256 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1207 49 h91 kg_303_1207
    have h93 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1257 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1256 1 h92 kg_303_1256
    have h94 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1288 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1257 31 h93 kg_303_1257
    have h95 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1299 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1288 11 h94 kg_303_1288
    have h96 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1331 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1299 32 h95 kg_303_1299
    have h97 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1363 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1331 32 h96 kg_303_1331
    have h98 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1376 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1363 13 h97 kg_303_1363
    have h99 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1377 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1376 1 h98 kg_303_1376
    have h100 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1408 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1377 31 h99 kg_303_1377
    have h101 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1415 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1408 7 h100 kg_303_1408
    have h102 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1433 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1415 18 h101 kg_303_1415
    have h103 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1447 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1433 14 h102 kg_303_1433
    have h104 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1448 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1447 1 h103 kg_303_1447
    have h105 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1465 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1448 17 h104 kg_303_1448
    have h106 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1474 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1465 9 h105 kg_303_1465
    have h107 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1479 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1474 5 h106 kg_303_1474
    have h108 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1482 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1479 3 h107 kg_303_1479
    have h109 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 1528 = true := IPChk.allR_join (Pts.glueIB K303.lits KW_303) 0 1482 46 h108 kg_303_1482
    exact h109
  have hlen : K303.lits.length = 1528 := by decide
  intro k h1 h2
  obtain rfl : k = 303 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 303) K303.lits KW_303
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_76 : ∀ k, 304 ≤ k → k < 305 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 1045 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 2 = true := kb_304_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 2 2 h0 kb_304_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 4 14 h1 kb_304_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 18 2 h2 kb_304_18
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 20 6 h3 kb_304_20
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 26 3 h4 kb_304_26
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 29 27 h5 kb_304_29
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 56 2 h6 kb_304_56
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 58 6 h7 kb_304_58
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 64 2 h8 kb_304_64
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 66 22 h9 kb_304_66
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 88 3 h10 kb_304_88
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 91 6 h11 kb_304_91
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 97 2 h12 kb_304_97
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 99 49 h13 kb_304_99
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 148 2 h14 kb_304_148
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 150 15 h15 kb_304_150
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 165 8 h16 kb_304_165
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 173 1 h17 kb_304_173
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 174 4 h18 kb_304_174
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 178 10 h19 kb_304_178
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 188 1 h20 kb_304_188
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 189 12 h21 kb_304_189
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 201 7 h22 kb_304_201
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 208 12 h23 kb_304_208
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 220 15 h24 kb_304_220
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 235 2 h25 kb_304_235
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 237 23 h26 kb_304_237
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 260 7 h27 kb_304_260
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 267 14 h28 kb_304_267
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 281 1 h29 kb_304_281
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 282 2 h30 kb_304_282
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 284 7 h31 kb_304_284
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 291 3 h32 kb_304_291
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 314 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 294 20 h33 kb_304_294
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 314 3 h34 kb_304_314
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 318 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 317 1 h35 kb_304_317
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 318 2 h36 kb_304_318
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 320 3 h37 kb_304_320
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 323 8 h38 kb_304_323
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 331 13 h39 kb_304_331
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 344 10 h40 kb_304_344
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 354 3 h41 kb_304_354
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 357 20 h42 kb_304_357
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 377 2 h43 kb_304_377
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 379 9 h44 kb_304_379
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 388 15 h45 kb_304_388
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 403 2 h46 kb_304_403
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 405 3 h47 kb_304_405
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 408 1 h48 kb_304_408
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 409 2 h49 kb_304_409
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 411 3 h50 kb_304_411
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 414 17 h51 kb_304_414
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 431 14 h52 kb_304_431
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 445 1 h53 kb_304_445
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 446 1 h54 kb_304_446
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 447 1 h55 kb_304_447
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 448 2 h56 kb_304_448
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 450 24 h57 kb_304_450
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 474 9 h58 kb_304_474
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 483 6 h59 kb_304_483
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 489 22 h60 kb_304_489
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 511 4 h61 kb_304_511
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 515 2 h62 kb_304_515
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 517 22 h63 kb_304_517
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 569 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 539 30 h64 kb_304_539
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 569 38 h65 kb_304_569
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 607 6 h66 kb_304_607
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 615 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 613 2 h67 kb_304_613
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 615 18 h68 kb_304_615
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 633 1 h69 kb_304_633
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 634 2 h70 kb_304_634
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 636 4 h71 kb_304_636
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 640 22 h72 kb_304_640
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 662 1 h73 kb_304_662
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 663 2 h74 kb_304_663
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 665 7 h75 kb_304_665
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 672 17 h76 kb_304_672
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 708 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 689 19 h77 kb_304_689
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 708 12 h78 kb_304_708
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 727 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 720 7 h79 kb_304_720
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 728 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 727 1 h80 kb_304_727
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 728 3 h81 kb_304_728
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 731 4 h82 kb_304_731
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 751 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 735 16 h83 kb_304_735
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 753 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 751 2 h84 kb_304_751
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 753 18 h85 kb_304_753
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 772 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 771 1 h86 kb_304_771
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 790 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 772 18 h87 kb_304_772
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 792 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 790 2 h88 kb_304_790
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 799 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 792 7 h89 kb_304_792
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 799 9 h90 kb_304_799
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 808 15 h91 kb_304_808
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 823 21 h92 kb_304_823
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 844 31 h93 kb_304_844
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 911 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 875 36 h94 kb_304_875
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 911 13 h95 kb_304_911
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 944 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 924 20 h96 kb_304_924
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 947 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 944 3 h97 kb_304_944
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 957 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 947 10 h98 kb_304_947
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 964 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 957 7 h99 kb_304_957
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 966 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 964 2 h100 kb_304_964
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 995 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 966 29 h101 kb_304_966
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 995 33 h102 kb_304_995
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 1045 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K304.lits.getD i 0)) 0 1028 17 h103 kb_304_1028
    exact h104
  have hg : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 1045 = true := by
    have h0 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 2 = true := kg_304_0
    have h1 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 4 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 2 2 h0 kg_304_2
    have h2 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 18 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 4 14 h1 kg_304_4
    have h3 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 20 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 18 2 h2 kg_304_18
    have h4 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 26 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 20 6 h3 kg_304_20
    have h5 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 29 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 26 3 h4 kg_304_26
    have h6 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 56 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 29 27 h5 kg_304_29
    have h7 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 58 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 56 2 h6 kg_304_56
    have h8 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 64 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 58 6 h7 kg_304_58
    have h9 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 66 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 64 2 h8 kg_304_64
    have h10 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 88 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 66 22 h9 kg_304_66
    have h11 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 91 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 88 3 h10 kg_304_88
    have h12 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 97 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 91 6 h11 kg_304_91
    have h13 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 99 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 97 2 h12 kg_304_97
    have h14 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 148 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 99 49 h13 kg_304_99
    have h15 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 150 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 148 2 h14 kg_304_148
    have h16 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 165 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 150 15 h15 kg_304_150
    have h17 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 173 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 165 8 h16 kg_304_165
    have h18 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 174 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 173 1 h17 kg_304_173
    have h19 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 178 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 174 4 h18 kg_304_174
    have h20 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 188 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 178 10 h19 kg_304_178
    have h21 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 189 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 188 1 h20 kg_304_188
    have h22 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 201 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 189 12 h21 kg_304_189
    have h23 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 208 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 201 7 h22 kg_304_201
    have h24 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 220 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 208 12 h23 kg_304_208
    have h25 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 235 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 220 15 h24 kg_304_220
    have h26 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 237 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 235 2 h25 kg_304_235
    have h27 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 260 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 237 23 h26 kg_304_237
    have h28 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 267 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 260 7 h27 kg_304_260
    have h29 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 281 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 267 14 h28 kg_304_267
    have h30 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 282 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 281 1 h29 kg_304_281
    have h31 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 284 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 282 2 h30 kg_304_282
    have h32 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 291 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 284 7 h31 kg_304_284
    have h33 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 294 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 291 3 h32 kg_304_291
    have h34 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 314 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 294 20 h33 kg_304_294
    have h35 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 317 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 314 3 h34 kg_304_314
    have h36 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 318 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 317 1 h35 kg_304_317
    have h37 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 320 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 318 2 h36 kg_304_318
    have h38 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 323 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 320 3 h37 kg_304_320
    have h39 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 331 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 323 8 h38 kg_304_323
    have h40 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 344 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 331 13 h39 kg_304_331
    have h41 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 354 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 344 10 h40 kg_304_344
    have h42 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 357 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 354 3 h41 kg_304_354
    have h43 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 377 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 357 20 h42 kg_304_357
    have h44 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 379 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 377 2 h43 kg_304_377
    have h45 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 388 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 379 9 h44 kg_304_379
    have h46 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 403 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 388 15 h45 kg_304_388
    have h47 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 405 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 403 2 h46 kg_304_403
    have h48 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 408 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 405 3 h47 kg_304_405
    have h49 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 409 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 408 1 h48 kg_304_408
    have h50 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 411 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 409 2 h49 kg_304_409
    have h51 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 414 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 411 3 h50 kg_304_411
    have h52 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 431 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 414 17 h51 kg_304_414
    have h53 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 445 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 431 14 h52 kg_304_431
    have h54 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 446 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 445 1 h53 kg_304_445
    have h55 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 447 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 446 1 h54 kg_304_446
    have h56 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 448 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 447 1 h55 kg_304_447
    have h57 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 450 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 448 2 h56 kg_304_448
    have h58 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 474 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 450 24 h57 kg_304_450
    have h59 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 483 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 474 9 h58 kg_304_474
    have h60 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 489 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 483 6 h59 kg_304_483
    have h61 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 511 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 489 22 h60 kg_304_489
    have h62 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 515 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 511 4 h61 kg_304_511
    have h63 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 517 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 515 2 h62 kg_304_515
    have h64 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 539 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 517 22 h63 kg_304_517
    have h65 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 569 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 539 30 h64 kg_304_539
    have h66 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 607 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 569 38 h65 kg_304_569
    have h67 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 613 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 607 6 h66 kg_304_607
    have h68 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 615 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 613 2 h67 kg_304_613
    have h69 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 633 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 615 18 h68 kg_304_615
    have h70 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 634 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 633 1 h69 kg_304_633
    have h71 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 636 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 634 2 h70 kg_304_634
    have h72 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 640 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 636 4 h71 kg_304_636
    have h73 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 662 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 640 22 h72 kg_304_640
    have h74 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 663 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 662 1 h73 kg_304_662
    have h75 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 665 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 663 2 h74 kg_304_663
    have h76 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 672 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 665 7 h75 kg_304_665
    have h77 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 689 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 672 17 h76 kg_304_672
    have h78 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 708 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 689 19 h77 kg_304_689
    have h79 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 720 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 708 12 h78 kg_304_708
    have h80 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 727 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 720 7 h79 kg_304_720
    have h81 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 728 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 727 1 h80 kg_304_727
    have h82 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 731 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 728 3 h81 kg_304_728
    have h83 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 735 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 731 4 h82 kg_304_731
    have h84 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 751 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 735 16 h83 kg_304_735
    have h85 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 753 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 751 2 h84 kg_304_751
    have h86 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 771 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 753 18 h85 kg_304_753
    have h87 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 772 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 771 1 h86 kg_304_771
    have h88 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 790 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 772 18 h87 kg_304_772
    have h89 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 792 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 790 2 h88 kg_304_790
    have h90 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 799 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 792 7 h89 kg_304_792
    have h91 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 808 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 799 9 h90 kg_304_799
    have h92 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 823 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 808 15 h91 kg_304_808
    have h93 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 844 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 823 21 h92 kg_304_823
    have h94 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 875 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 844 31 h93 kg_304_844
    have h95 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 911 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 875 36 h94 kg_304_875
    have h96 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 924 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 911 13 h95 kg_304_911
    have h97 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 944 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 924 20 h96 kg_304_924
    have h98 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 947 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 944 3 h97 kg_304_944
    have h99 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 957 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 947 10 h98 kg_304_947
    have h100 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 964 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 957 7 h99 kg_304_957
    have h101 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 966 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 964 2 h100 kg_304_964
    have h102 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 995 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 966 29 h101 kg_304_966
    have h103 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 1028 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 995 33 h102 kg_304_995
    have h104 : IPChk.allR (Pts.glueIB K304.lits KW_304) 0 1045 = true := IPChk.allR_join (Pts.glueIB K304.lits KW_304) 0 1028 17 h103 kg_304_1028
    exact h104
  have hlen : K304.lits.length = 1045 := by decide
  intro k h1 h2
  obtain rfl : k = 304 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 304) K304.lits KW_304
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_77 : ∀ k, 305 ≤ k → k < 306 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_305 JW_305 305 1 jr_305
theorem jr6_78 : ∀ k, 306 ≤ k → k < 307 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 956 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 1 = true := kb_306_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 1 2 h0 kb_306_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 3 29 h1 kb_306_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 32 2 h2 kb_306_32
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 34 6 h3 kb_306_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 40 2 h4 kb_306_40
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 42 30 h5 kb_306_42
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 72 14 h6 kb_306_72
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 86 11 h7 kb_306_86
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 97 24 h8 kb_306_97
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 121 7 h9 kb_306_121
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 128 21 h10 kb_306_128
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 149 11 h11 kb_306_149
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 160 2 h12 kb_306_160
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 162 19 h13 kb_306_162
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 181 6 h14 kb_306_181
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 187 2 h15 kb_306_187
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 189 21 h16 kb_306_189
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 210 2 h17 kb_306_210
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 212 1 h18 kb_306_212
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 213 1 h19 kb_306_213
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 214 13 h20 kb_306_214
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 227 2 h21 kb_306_227
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 229 22 h22 kb_306_229
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 251 1 h23 kb_306_251
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 252 2 h24 kb_306_252
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 254 9 h25 kb_306_254
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 263 19 h26 kb_306_263
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 282 1 h27 kb_306_282
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 283 1 h28 kb_306_283
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 284 1 h29 kb_306_284
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 285 25 h30 kb_306_285
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 310 1 h31 kb_306_310
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 311 1 h32 kb_306_311
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 312 9 h33 kb_306_312
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 321 47 h34 kb_306_321
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 368 9 h35 kb_306_368
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 377 2 h36 kb_306_377
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 379 22 h37 kb_306_379
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 401 29 h38 kb_306_401
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 430 15 h39 kb_306_430
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 445 28 h40 kb_306_445
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 473 6 h41 kb_306_473
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 479 10 h42 kb_306_479
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 489 15 h43 kb_306_489
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 504 2 h44 kb_306_504
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 506 2 h45 kb_306_506
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 508 7 h46 kb_306_508
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 515 20 h47 kb_306_515
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 536 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 535 1 h48 kb_306_535
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 536 2 h49 kb_306_536
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 538 6 h50 kb_306_538
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 544 2 h51 kb_306_544
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 546 17 h52 kb_306_546
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 563 16 h53 kb_306_563
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 579 9 h54 kb_306_579
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 588 1 h55 kb_306_588
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 589 2 h56 kb_306_589
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 591 22 h57 kb_306_591
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 614 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 613 1 h58 kb_306_613
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 615 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 614 1 h59 kb_306_614
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 617 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 615 2 h60 kb_306_615
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 617 1 h61 kb_306_617
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 618 2 h62 kb_306_618
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 621 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 620 1 h63 kb_306_620
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 621 3 h64 kb_306_621
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 644 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 624 20 h65 kb_306_624
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 646 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 644 2 h66 kb_306_644
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 646 11 h67 kb_306_646
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 657 13 h68 kb_306_657
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 670 2 h69 kb_306_670
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 672 3 h70 kb_306_672
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 675 17 h71 kb_306_675
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 694 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 692 2 h72 kb_306_692
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 694 1 h73 kb_306_694
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 695 2 h74 kb_306_695
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 704 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 697 7 h75 kb_306_697
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 704 37 h76 kb_306_704
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 801 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 741 60 h77 kb_306_741
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 801 1 h78 kb_306_801
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 832 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 802 30 h79 kb_306_802
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 842 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 832 10 h80 kb_306_832
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 845 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 842 3 h81 kb_306_842
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 853 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 845 8 h82 kb_306_845
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 854 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 853 1 h83 kb_306_853
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 856 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 854 2 h84 kb_306_854
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 856 30 h85 kb_306_856
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 886 35 h86 kb_306_886
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 921 1 h87 kb_306_921
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 924 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 922 2 h88 kb_306_922
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 937 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 924 13 h89 kb_306_924
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 956 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K306.lits.getD i 0)) 0 937 19 h90 kb_306_937
    exact h91
  have hg : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 956 = true := by
    have h0 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 1 = true := kg_306_0
    have h1 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 3 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 1 2 h0 kg_306_1
    have h2 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 32 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 3 29 h1 kg_306_3
    have h3 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 34 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 32 2 h2 kg_306_32
    have h4 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 40 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 34 6 h3 kg_306_34
    have h5 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 42 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 40 2 h4 kg_306_40
    have h6 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 72 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 42 30 h5 kg_306_42
    have h7 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 86 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 72 14 h6 kg_306_72
    have h8 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 97 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 86 11 h7 kg_306_86
    have h9 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 121 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 97 24 h8 kg_306_97
    have h10 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 128 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 121 7 h9 kg_306_121
    have h11 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 149 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 128 21 h10 kg_306_128
    have h12 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 160 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 149 11 h11 kg_306_149
    have h13 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 162 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 160 2 h12 kg_306_160
    have h14 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 181 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 162 19 h13 kg_306_162
    have h15 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 187 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 181 6 h14 kg_306_181
    have h16 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 189 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 187 2 h15 kg_306_187
    have h17 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 210 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 189 21 h16 kg_306_189
    have h18 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 212 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 210 2 h17 kg_306_210
    have h19 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 213 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 212 1 h18 kg_306_212
    have h20 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 214 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 213 1 h19 kg_306_213
    have h21 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 227 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 214 13 h20 kg_306_214
    have h22 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 229 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 227 2 h21 kg_306_227
    have h23 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 251 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 229 22 h22 kg_306_229
    have h24 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 252 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 251 1 h23 kg_306_251
    have h25 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 254 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 252 2 h24 kg_306_252
    have h26 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 263 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 254 9 h25 kg_306_254
    have h27 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 282 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 263 19 h26 kg_306_263
    have h28 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 283 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 282 1 h27 kg_306_282
    have h29 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 284 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 283 1 h28 kg_306_283
    have h30 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 285 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 284 1 h29 kg_306_284
    have h31 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 310 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 285 25 h30 kg_306_285
    have h32 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 311 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 310 1 h31 kg_306_310
    have h33 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 312 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 311 1 h32 kg_306_311
    have h34 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 321 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 312 9 h33 kg_306_312
    have h35 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 368 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 321 47 h34 kg_306_321
    have h36 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 377 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 368 9 h35 kg_306_368
    have h37 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 379 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 377 2 h36 kg_306_377
    have h38 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 401 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 379 22 h37 kg_306_379
    have h39 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 430 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 401 29 h38 kg_306_401
    have h40 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 445 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 430 15 h39 kg_306_430
    have h41 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 473 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 445 28 h40 kg_306_445
    have h42 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 479 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 473 6 h41 kg_306_473
    have h43 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 489 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 479 10 h42 kg_306_479
    have h44 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 504 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 489 15 h43 kg_306_489
    have h45 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 506 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 504 2 h44 kg_306_504
    have h46 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 508 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 506 2 h45 kg_306_506
    have h47 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 515 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 508 7 h46 kg_306_508
    have h48 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 535 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 515 20 h47 kg_306_515
    have h49 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 536 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 535 1 h48 kg_306_535
    have h50 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 538 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 536 2 h49 kg_306_536
    have h51 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 544 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 538 6 h50 kg_306_538
    have h52 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 546 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 544 2 h51 kg_306_544
    have h53 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 563 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 546 17 h52 kg_306_546
    have h54 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 579 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 563 16 h53 kg_306_563
    have h55 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 588 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 579 9 h54 kg_306_579
    have h56 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 589 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 588 1 h55 kg_306_588
    have h57 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 591 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 589 2 h56 kg_306_589
    have h58 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 613 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 591 22 h57 kg_306_591
    have h59 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 614 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 613 1 h58 kg_306_613
    have h60 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 615 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 614 1 h59 kg_306_614
    have h61 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 617 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 615 2 h60 kg_306_615
    have h62 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 618 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 617 1 h61 kg_306_617
    have h63 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 620 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 618 2 h62 kg_306_618
    have h64 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 621 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 620 1 h63 kg_306_620
    have h65 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 624 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 621 3 h64 kg_306_621
    have h66 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 644 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 624 20 h65 kg_306_624
    have h67 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 646 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 644 2 h66 kg_306_644
    have h68 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 657 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 646 11 h67 kg_306_646
    have h69 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 670 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 657 13 h68 kg_306_657
    have h70 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 672 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 670 2 h69 kg_306_670
    have h71 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 675 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 672 3 h70 kg_306_672
    have h72 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 692 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 675 17 h71 kg_306_675
    have h73 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 694 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 692 2 h72 kg_306_692
    have h74 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 695 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 694 1 h73 kg_306_694
    have h75 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 697 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 695 2 h74 kg_306_695
    have h76 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 704 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 697 7 h75 kg_306_697
    have h77 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 741 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 704 37 h76 kg_306_704
    have h78 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 801 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 741 60 h77 kg_306_741
    have h79 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 802 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 801 1 h78 kg_306_801
    have h80 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 832 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 802 30 h79 kg_306_802
    have h81 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 842 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 832 10 h80 kg_306_832
    have h82 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 845 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 842 3 h81 kg_306_842
    have h83 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 853 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 845 8 h82 kg_306_845
    have h84 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 854 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 853 1 h83 kg_306_853
    have h85 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 856 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 854 2 h84 kg_306_854
    have h86 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 886 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 856 30 h85 kg_306_856
    have h87 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 921 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 886 35 h86 kg_306_886
    have h88 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 922 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 921 1 h87 kg_306_921
    have h89 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 924 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 922 2 h88 kg_306_922
    have h90 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 937 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 924 13 h89 kg_306_924
    have h91 : IPChk.allR (Pts.glueIB K306.lits KW_306) 0 956 = true := IPChk.allR_join (Pts.glueIB K306.lits KW_306) 0 937 19 h90 kg_306_937
    exact h91
  have hlen : K306.lits.length = 956 := by decide
  intro k h1 h2
  obtain rfl : k = 306 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 306) K306.lits KW_306
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_79 : ∀ k, 307 ≤ k → k < 314 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_307 JW_307 307 7 jr_307
theorem jr6_80 : ∀ k, 314 ≤ k → k < 315 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 167 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 2 = true := kb_314_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 2 8 h0 kb_314_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 10 22 h1 kb_314_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 32 1 h2 kb_314_32
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 33 2 h3 kb_314_33
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 35 2 h4 kb_314_35
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 37 1 h5 kb_314_37
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 38 7 h6 kb_314_38
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 45 10 h7 kb_314_45
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 55 21 h8 kb_314_55
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 76 1 h9 kb_314_76
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 77 10 h10 kb_314_77
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 87 1 h11 kb_314_87
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 88 2 h12 kb_314_88
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 90 1 h13 kb_314_90
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 91 7 h14 kb_314_91
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 98 28 h15 kb_314_98
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 126 19 h16 kb_314_126
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 145 2 h17 kb_314_145
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 147 1 h18 kb_314_147
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 148 2 h19 kb_314_148
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 150 2 h20 kb_314_150
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 152 3 h21 kb_314_152
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 155 2 h22 kb_314_155
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 157 2 h23 kb_314_157
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 159 1 h24 kb_314_159
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 160 5 h25 kb_314_160
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 165 1 h26 kb_314_165
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 0 166 1 h27 kb_314_166
    exact h28
  have hg : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 167 = true := by
    have h0 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 2 = true := kg_314_0
    have h1 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 10 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 2 8 h0 kg_314_2
    have h2 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 32 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 10 22 h1 kg_314_10
    have h3 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 33 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 32 1 h2 kg_314_32
    have h4 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 35 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 33 2 h3 kg_314_33
    have h5 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 37 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 35 2 h4 kg_314_35
    have h6 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 38 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 37 1 h5 kg_314_37
    have h7 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 45 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 38 7 h6 kg_314_38
    have h8 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 55 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 45 10 h7 kg_314_45
    have h9 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 76 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 55 21 h8 kg_314_55
    have h10 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 77 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 76 1 h9 kg_314_76
    have h11 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 87 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 77 10 h10 kg_314_77
    have h12 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 88 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 87 1 h11 kg_314_87
    have h13 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 90 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 88 2 h12 kg_314_88
    have h14 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 91 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 90 1 h13 kg_314_90
    have h15 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 98 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 91 7 h14 kg_314_91
    have h16 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 126 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 98 28 h15 kg_314_98
    have h17 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 145 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 126 19 h16 kg_314_126
    have h18 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 147 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 145 2 h17 kg_314_145
    have h19 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 148 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 147 1 h18 kg_314_147
    have h20 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 150 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 148 2 h19 kg_314_148
    have h21 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 152 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 150 2 h20 kg_314_150
    have h22 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 155 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 152 3 h21 kg_314_152
    have h23 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 157 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 155 2 h22 kg_314_155
    have h24 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 159 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 157 2 h23 kg_314_157
    have h25 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 160 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 159 1 h24 kg_314_159
    have h26 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 165 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 160 5 h25 kg_314_160
    have h27 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 166 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 165 1 h26 kg_314_165
    have h28 : IPChk.allR (Pts.glueIB K314.lits KW_314) 0 167 = true := IPChk.allR_join (Pts.glueIB K314.lits KW_314) 0 166 1 h27 kg_314_166
    exact h28
  have hlen : K314.lits.length = 167 := by decide
  intro k h1 h2
  obtain rfl : k = 314 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 314) K314.lits KW_314
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_81 : ∀ k, 315 ≤ k → k < 362 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_315 JW_315 315 47 jr_315
theorem jr6_82 : ∀ k, 362 ≤ k → k < 363 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_315 JW_315 362 1 jr_362
theorem jr6_83 : ∀ k, 363 ≤ k → k < 364 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 832 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 15 = true := kb_363_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 15 12 h0 kb_363_15
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 27 3 h1 kb_363_27
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 30 4 h2 kb_363_30
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 65 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 34 31 h3 kb_363_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 71 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 65 6 h4 kb_363_65
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 71 2 h5 kb_363_71
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 73 29 h6 kb_363_73
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 102 9 h7 kb_363_102
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 111 20 h8 kb_363_111
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 131 11 h9 kb_363_131
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 142 3 h10 kb_363_142
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 145 9 h11 kb_363_145
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 154 10 h12 kb_363_154
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 164 2 h13 kb_363_164
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 166 17 h14 kb_363_166
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 183 2 h15 kb_363_183
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 185 8 h16 kb_363_185
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 193 1 h17 kb_363_193
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 194 1 h18 kb_363_194
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 195 1 h19 kb_363_195
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 196 21 h20 kb_363_196
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 217 15 h21 kb_363_217
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 232 4 h22 kb_363_232
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 236 16 h23 kb_363_236
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 252 8 h24 kb_363_252
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 260 26 h25 kb_363_260
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 286 2 h26 kb_363_286
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 288 14 h27 kb_363_288
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 302 13 h28 kb_363_302
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 315 2 h29 kb_363_315
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 317 4 h30 kb_363_317
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 321 2 h31 kb_363_321
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 323 10 h32 kb_363_323
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 333 2 h33 kb_363_333
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 335 4 h34 kb_363_335
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 339 2 h35 kb_363_339
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 341 11 h36 kb_363_341
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 352 12 h37 kb_363_352
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 364 11 h38 kb_363_364
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 375 30 h39 kb_363_375
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 405 4 h40 kb_363_405
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 409 2 h41 kb_363_409
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 411 12 h42 kb_363_411
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 423 5 h43 kb_363_423
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 428 11 h44 kb_363_428
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 439 6 h45 kb_363_439
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 445 21 h46 kb_363_445
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 466 21 h47 kb_363_466
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 487 18 h48 kb_363_487
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 505 6 h49 kb_363_505
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 511 3 h50 kb_363_511
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 514 18 h51 kb_363_514
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 532 30 h52 kb_363_532
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 604 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 562 42 h53 kb_363_562
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 604 30 h54 kb_363_604
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 634 18 h55 kb_363_634
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 652 31 h56 kb_363_652
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 683 24 h57 kb_363_683
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 727 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 707 20 h58 kb_363_707
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 727 4 h59 kb_363_727
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 731 2 h60 kb_363_731
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 743 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 733 10 h61 kb_363_733
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 759 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 743 16 h62 kb_363_743
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 768 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 759 9 h63 kb_363_759
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 768 3 h64 kb_363_768
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 805 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 771 34 h65 kb_363_771
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 832 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K363.lits.getD i 0)) 0 805 27 h66 kb_363_805
    exact h67
  have hg : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 832 = true := by
    have h0 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 15 = true := kg_363_0
    have h1 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 27 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 15 12 h0 kg_363_15
    have h2 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 30 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 27 3 h1 kg_363_27
    have h3 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 34 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 30 4 h2 kg_363_30
    have h4 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 65 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 34 31 h3 kg_363_34
    have h5 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 71 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 65 6 h4 kg_363_65
    have h6 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 73 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 71 2 h5 kg_363_71
    have h7 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 102 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 73 29 h6 kg_363_73
    have h8 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 111 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 102 9 h7 kg_363_102
    have h9 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 131 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 111 20 h8 kg_363_111
    have h10 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 142 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 131 11 h9 kg_363_131
    have h11 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 145 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 142 3 h10 kg_363_142
    have h12 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 154 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 145 9 h11 kg_363_145
    have h13 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 164 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 154 10 h12 kg_363_154
    have h14 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 166 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 164 2 h13 kg_363_164
    have h15 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 183 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 166 17 h14 kg_363_166
    have h16 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 185 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 183 2 h15 kg_363_183
    have h17 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 193 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 185 8 h16 kg_363_185
    have h18 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 194 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 193 1 h17 kg_363_193
    have h19 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 195 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 194 1 h18 kg_363_194
    have h20 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 196 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 195 1 h19 kg_363_195
    have h21 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 217 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 196 21 h20 kg_363_196
    have h22 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 232 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 217 15 h21 kg_363_217
    have h23 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 236 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 232 4 h22 kg_363_232
    have h24 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 252 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 236 16 h23 kg_363_236
    have h25 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 260 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 252 8 h24 kg_363_252
    have h26 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 286 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 260 26 h25 kg_363_260
    have h27 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 288 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 286 2 h26 kg_363_286
    have h28 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 302 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 288 14 h27 kg_363_288
    have h29 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 315 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 302 13 h28 kg_363_302
    have h30 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 317 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 315 2 h29 kg_363_315
    have h31 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 321 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 317 4 h30 kg_363_317
    have h32 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 323 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 321 2 h31 kg_363_321
    have h33 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 333 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 323 10 h32 kg_363_323
    have h34 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 335 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 333 2 h33 kg_363_333
    have h35 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 339 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 335 4 h34 kg_363_335
    have h36 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 341 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 339 2 h35 kg_363_339
    have h37 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 352 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 341 11 h36 kg_363_341
    have h38 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 364 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 352 12 h37 kg_363_352
    have h39 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 375 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 364 11 h38 kg_363_364
    have h40 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 405 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 375 30 h39 kg_363_375
    have h41 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 409 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 405 4 h40 kg_363_405
    have h42 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 411 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 409 2 h41 kg_363_409
    have h43 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 423 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 411 12 h42 kg_363_411
    have h44 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 428 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 423 5 h43 kg_363_423
    have h45 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 439 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 428 11 h44 kg_363_428
    have h46 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 445 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 439 6 h45 kg_363_439
    have h47 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 466 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 445 21 h46 kg_363_445
    have h48 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 487 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 466 21 h47 kg_363_466
    have h49 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 505 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 487 18 h48 kg_363_487
    have h50 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 511 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 505 6 h49 kg_363_505
    have h51 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 514 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 511 3 h50 kg_363_511
    have h52 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 532 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 514 18 h51 kg_363_514
    have h53 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 562 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 532 30 h52 kg_363_532
    have h54 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 604 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 562 42 h53 kg_363_562
    have h55 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 634 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 604 30 h54 kg_363_604
    have h56 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 652 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 634 18 h55 kg_363_634
    have h57 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 683 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 652 31 h56 kg_363_652
    have h58 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 707 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 683 24 h57 kg_363_683
    have h59 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 727 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 707 20 h58 kg_363_707
    have h60 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 731 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 727 4 h59 kg_363_727
    have h61 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 733 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 731 2 h60 kg_363_731
    have h62 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 743 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 733 10 h61 kg_363_733
    have h63 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 759 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 743 16 h62 kg_363_743
    have h64 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 768 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 759 9 h63 kg_363_759
    have h65 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 771 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 768 3 h64 kg_363_768
    have h66 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 805 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 771 34 h65 kg_363_771
    have h67 : IPChk.allR (Pts.glueIB K363.lits KW_363) 0 832 = true := IPChk.allR_join (Pts.glueIB K363.lits KW_363) 0 805 27 h66 kg_363_805
    exact h67
  have hlen : K363.lits.length = 832 := by decide
  intro k h1 h2
  obtain rfl : k = 363 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 363) K363.lits KW_363
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_84 : ∀ k, 364 ≤ k → k < 365 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 280 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 9 = true := kb_364_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 9 2 h0 kb_364_9
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 11 17 h1 kb_364_11
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 28 7 h2 kb_364_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 35 14 h3 kb_364_35
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 49 11 h4 kb_364_49
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 60 26 h5 kb_364_60
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 86 9 h6 kb_364_86
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 95 10 h7 kb_364_95
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 105 17 h8 kb_364_105
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 122 2 h9 kb_364_122
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 124 4 h10 kb_364_124
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 128 20 h11 kb_364_128
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 148 37 h12 kb_364_148
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 185 52 h13 kb_364_185
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K364.lits.getD i 0)) 0 237 43 h14 kb_364_237
    exact h15
  have hg : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 280 = true := by
    have h0 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 9 = true := kg_364_0
    have h1 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 11 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 9 2 h0 kg_364_9
    have h2 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 28 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 11 17 h1 kg_364_11
    have h3 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 35 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 28 7 h2 kg_364_28
    have h4 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 49 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 35 14 h3 kg_364_35
    have h5 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 60 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 49 11 h4 kg_364_49
    have h6 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 86 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 60 26 h5 kg_364_60
    have h7 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 95 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 86 9 h6 kg_364_86
    have h8 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 105 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 95 10 h7 kg_364_95
    have h9 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 122 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 105 17 h8 kg_364_105
    have h10 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 124 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 122 2 h9 kg_364_122
    have h11 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 128 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 124 4 h10 kg_364_124
    have h12 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 148 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 128 20 h11 kg_364_128
    have h13 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 185 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 148 37 h12 kg_364_148
    have h14 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 237 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 185 52 h13 kg_364_185
    have h15 : IPChk.allR (Pts.glueIB K364.lits KW_364) 0 280 = true := IPChk.allR_join (Pts.glueIB K364.lits KW_364) 0 237 43 h14 kg_364_237
    exact h15
  have hlen : K364.lits.length = 280 := by decide
  intro k h1 h2
  obtain rfl : k = 364 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 364) K364.lits KW_364
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_85 : ∀ k, 365 ≤ k → k < 366 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_365 JW_365 365 1 jr_365
theorem jr6_86 : ∀ k, 366 ≤ k → k < 367 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 597 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 1 = true := kb_366_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 1 2 h0 kb_366_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 3 29 h1 kb_366_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 32 2 h2 kb_366_32
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 34 7 h3 kb_366_34
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 41 21 h4 kb_366_41
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 62 55 h5 kb_366_62
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 117 15 h6 kb_366_117
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 132 4 h7 kb_366_132
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 136 15 h8 kb_366_136
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 151 41 h9 kb_366_151
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 192 2 h10 kb_366_192
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 194 15 h11 kb_366_194
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 209 1 h12 kb_366_209
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 210 4 h13 kb_366_210
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 214 1 h14 kb_366_214
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 215 1 h15 kb_366_215
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 216 4 h16 kb_366_216
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 220 13 h17 kb_366_220
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 233 18 h18 kb_366_233
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 251 6 h19 kb_366_251
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 257 2 h20 kb_366_257
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 259 18 h21 kb_366_259
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 277 11 h22 kb_366_277
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 288 2 h23 kb_366_288
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 290 22 h24 kb_366_290
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 312 1 h25 kb_366_312
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 314 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 313 1 h26 kb_366_313
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 314 2 h27 kb_366_314
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 316 10 h28 kb_366_316
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 326 14 h29 kb_366_326
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 340 1 h30 kb_366_340
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 341 20 h31 kb_366_341
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 361 11 h32 kb_366_361
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 372 1 h33 kb_366_372
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 373 2 h34 kb_366_373
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 375 1 h35 kb_366_375
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 376 1 h36 kb_366_376
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 377 6 h37 kb_366_377
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 383 20 h38 kb_366_383
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 403 1 h39 kb_366_403
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 404 1 h40 kb_366_404
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 405 2 h41 kb_366_405
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 407 3 h42 kb_366_407
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 410 1 h43 kb_366_410
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 411 2 h44 kb_366_411
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 413 20 h45 kb_366_413
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 433 14 h46 kb_366_433
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 447 18 h47 kb_366_447
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 465 7 h48 kb_366_465
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 472 1 h49 kb_366_472
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 473 33 h50 kb_366_473
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 506 38 h51 kb_366_506
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 544 3 h52 kb_366_544
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 547 7 h53 kb_366_547
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 554 2 h54 kb_366_554
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 556 3 h55 kb_366_556
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K366.lits.getD i 0)) 0 559 38 h56 kb_366_559
    exact h57
  have hg : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 597 = true := by
    have h0 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 1 = true := kg_366_0
    have h1 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 3 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 1 2 h0 kg_366_1
    have h2 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 32 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 3 29 h1 kg_366_3
    have h3 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 34 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 32 2 h2 kg_366_32
    have h4 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 41 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 34 7 h3 kg_366_34
    have h5 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 62 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 41 21 h4 kg_366_41
    have h6 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 117 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 62 55 h5 kg_366_62
    have h7 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 132 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 117 15 h6 kg_366_117
    have h8 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 136 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 132 4 h7 kg_366_132
    have h9 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 151 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 136 15 h8 kg_366_136
    have h10 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 192 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 151 41 h9 kg_366_151
    have h11 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 194 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 192 2 h10 kg_366_192
    have h12 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 209 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 194 15 h11 kg_366_194
    have h13 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 210 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 209 1 h12 kg_366_209
    have h14 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 214 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 210 4 h13 kg_366_210
    have h15 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 215 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 214 1 h14 kg_366_214
    have h16 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 216 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 215 1 h15 kg_366_215
    have h17 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 220 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 216 4 h16 kg_366_216
    have h18 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 233 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 220 13 h17 kg_366_220
    have h19 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 251 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 233 18 h18 kg_366_233
    have h20 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 257 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 251 6 h19 kg_366_251
    have h21 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 259 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 257 2 h20 kg_366_257
    have h22 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 277 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 259 18 h21 kg_366_259
    have h23 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 288 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 277 11 h22 kg_366_277
    have h24 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 290 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 288 2 h23 kg_366_288
    have h25 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 312 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 290 22 h24 kg_366_290
    have h26 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 313 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 312 1 h25 kg_366_312
    have h27 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 314 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 313 1 h26 kg_366_313
    have h28 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 316 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 314 2 h27 kg_366_314
    have h29 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 326 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 316 10 h28 kg_366_316
    have h30 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 340 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 326 14 h29 kg_366_326
    have h31 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 341 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 340 1 h30 kg_366_340
    have h32 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 361 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 341 20 h31 kg_366_341
    have h33 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 372 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 361 11 h32 kg_366_361
    have h34 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 373 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 372 1 h33 kg_366_372
    have h35 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 375 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 373 2 h34 kg_366_373
    have h36 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 376 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 375 1 h35 kg_366_375
    have h37 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 377 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 376 1 h36 kg_366_376
    have h38 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 383 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 377 6 h37 kg_366_377
    have h39 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 403 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 383 20 h38 kg_366_383
    have h40 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 404 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 403 1 h39 kg_366_403
    have h41 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 405 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 404 1 h40 kg_366_404
    have h42 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 407 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 405 2 h41 kg_366_405
    have h43 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 410 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 407 3 h42 kg_366_407
    have h44 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 411 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 410 1 h43 kg_366_410
    have h45 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 413 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 411 2 h44 kg_366_411
    have h46 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 433 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 413 20 h45 kg_366_413
    have h47 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 447 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 433 14 h46 kg_366_433
    have h48 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 465 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 447 18 h47 kg_366_447
    have h49 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 472 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 465 7 h48 kg_366_465
    have h50 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 473 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 472 1 h49 kg_366_472
    have h51 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 506 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 473 33 h50 kg_366_473
    have h52 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 544 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 506 38 h51 kg_366_506
    have h53 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 547 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 544 3 h52 kg_366_544
    have h54 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 554 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 547 7 h53 kg_366_547
    have h55 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 556 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 554 2 h54 kg_366_554
    have h56 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 559 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 556 3 h55 kg_366_556
    have h57 : IPChk.allR (Pts.glueIB K366.lits KW_366) 0 597 = true := IPChk.allR_join (Pts.glueIB K366.lits KW_366) 0 559 38 h56 kg_366_559
    exact h57
  have hlen : K366.lits.length = 597 := by decide
  intro k h1 h2
  obtain rfl : k = 366 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 366) K366.lits KW_366
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_87 : ∀ k, 367 ≤ k → k < 393 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_367 JW_367 367 26 jr_367

theorem grp6_3 : ∀ k, 298 ≤ k → k < 393 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_71
  have a1 := Pts.fa_join a0 jr6_72
  have a2 := Pts.fa_join a1 jr6_73
  have a3 := Pts.fa_join a2 jr6_74
  have a4 := Pts.fa_join a3 jr6_75
  have a5 := Pts.fa_join a4 jr6_76
  have a6 := Pts.fa_join a5 jr6_77
  have a7 := Pts.fa_join a6 jr6_78
  have a8 := Pts.fa_join a7 jr6_79
  have a9 := Pts.fa_join a8 jr6_80
  have a10 := Pts.fa_join a9 jr6_81
  have a11 := Pts.fa_join a10 jr6_82
  have a12 := Pts.fa_join a11 jr6_83
  have a13 := Pts.fa_join a12 jr6_84
  have a14 := Pts.fa_join a13 jr6_85
  have a15 := Pts.fa_join a14 jr6_86
  have a16 := Pts.fa_join a15 jr6_87
  exact a16

end B334.E1x.Pts.S707
