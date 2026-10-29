import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J1733
import B334.E1x.Pts.S707.J1735
import B334.E1x.Pts.S707.J1739
import B334.E1x.Pts.S707.J1779
import B334.E1x.Pts.S707.J1781
import B334.E1x.Pts.S707.J1783
import B334.E1x.Pts.S707.J1829
import B334.E1x.Pts.S707.J1869
import B334.E1x.Pts.S707.J1898
import B334.E1x.Pts.S707.K1732L
import B334.E1x.Pts.S707.K1734L
import B334.E1x.Pts.S707.K1738L
import B334.E1x.Pts.S707.K1778L
import B334.E1x.Pts.S707.K1780L
import B334.E1x.Pts.S707.K1782L
import B334.E1x.Pts.S707.K1828L
import B334.E1x.Pts.S707.K1868L
import B334.E1x.Pts.S707.K1897L
import B334.E1x.Pts.S707.K1930L
import B334.E1x.Pts.S707.K1931L
import B334.E1x.Pts.S707.K1732Q0
import B334.E1x.Pts.S707.K1732Q1
import B334.E1x.Pts.S707.K1732Q2
import B334.E1x.Pts.S707.K1732Q3
import B334.E1x.Pts.S707.K1732Q4
import B334.E1x.Pts.S707.K1732Q5
import B334.E1x.Pts.S707.K1732Q6
import B334.E1x.Pts.S707.K1732Q7
import B334.E1x.Pts.S707.K1732Q8
import B334.E1x.Pts.S707.K1732Q9
import B334.E1x.Pts.S707.K1734Q0
import B334.E1x.Pts.S707.K1734Q1
import B334.E1x.Pts.S707.K1734Q2
import B334.E1x.Pts.S707.K1734Q3
import B334.E1x.Pts.S707.K1738Q0
import B334.E1x.Pts.S707.K1778Q0
import B334.E1x.Pts.S707.K1778Q1
import B334.E1x.Pts.S707.K1778Q2
import B334.E1x.Pts.S707.K1778Q3
import B334.E1x.Pts.S707.K1778Q4
import B334.E1x.Pts.S707.K1778Q5
import B334.E1x.Pts.S707.K1778Q6
import B334.E1x.Pts.S707.K1780Q0
import B334.E1x.Pts.S707.K1780Q1
import B334.E1x.Pts.S707.K1780Q2
import B334.E1x.Pts.S707.K1780Q3
import B334.E1x.Pts.S707.K1780Q4
import B334.E1x.Pts.S707.K1780Q5
import B334.E1x.Pts.S707.K1780Q6
import B334.E1x.Pts.S707.K1780Q7
import B334.E1x.Pts.S707.K1780Q8
import B334.E1x.Pts.S707.K1782Q0
import B334.E1x.Pts.S707.K1782Q1
import B334.E1x.Pts.S707.K1782Q2
import B334.E1x.Pts.S707.K1782Q3
import B334.E1x.Pts.S707.K1782Q4
import B334.E1x.Pts.S707.K1782Q5
import B334.E1x.Pts.S707.K1828Q0
import B334.E1x.Pts.S707.K1828Q1
import B334.E1x.Pts.S707.K1828Q2
import B334.E1x.Pts.S707.K1868Q0
import B334.E1x.Pts.S707.K1868Q1
import B334.E1x.Pts.S707.K1868Q2
import B334.E1x.Pts.S707.K1868Q3
import B334.E1x.Pts.S707.K1868Q4
import B334.E1x.Pts.S707.K1868Q5
import B334.E1x.Pts.S707.K1868Q6
import B334.E1x.Pts.S707.K1897Q0
import B334.E1x.Pts.S707.K1897Q1
import B334.E1x.Pts.S707.K1930Q0
import B334.E1x.Pts.S707.K1930Q1
import B334.E1x.Pts.S707.K1930Q2
import B334.E1x.Pts.S707.K1930Q3
import B334.E1x.Pts.S707.K1931Q0
import B334.E1x.Pts.S707.K1732Q10
import B334.E1x.Pts.S707.K1732Q11
import B334.E1x.Pts.S707.K1732Q12
import B334.E1x.Pts.S707.K1732Q13
import B334.E1x.Pts.S707.K1732Q14
import B334.E1x.Pts.S707.K1732Q15
import B334.E1x.Pts.S707.K1732Q16
import B334.E1x.Pts.S707.K1732Q17
import B334.E1x.Pts.S707.K1732Q18
import B334.E1x.Pts.S707.K1732Q19
import B334.E1x.Pts.S707.K1732Q20
import B334.E1x.Pts.S707.K1732Q21
import B334.E1x.Pts.S707.K1732Q22

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 1732 … 1931 (stage707_v6): the v5 Fin's job blocks r337 … r356 as
theorems, joined into `grp6_13` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_337 : ∀ k, 1732 ≤ k → k < 1733 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1500 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 4 = true := kb_1732_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 4 5 h0 kb_1732_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 9 1 h1 kb_1732_9
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 10 17 h2 kb_1732_10
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 27 5 h3 kb_1732_27
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 32 1 h4 kb_1732_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 33 11 h5 kb_1732_33
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 44 1 h6 kb_1732_44
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 45 17 h7 kb_1732_45
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 62 10 h8 kb_1732_62
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 72 1 h9 kb_1732_72
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 73 9 h10 kb_1732_73
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 82 98 h11 kb_1732_82
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 180 16 h12 kb_1732_180
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 196 2 h13 kb_1732_196
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 198 2 h14 kb_1732_198
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 200 3 h15 kb_1732_200
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 203 8 h16 kb_1732_203
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 211 4 h17 kb_1732_211
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 215 2 h18 kb_1732_215
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 217 6 h19 kb_1732_217
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 223 1 h20 kb_1732_223
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 224 1 h21 kb_1732_224
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 225 29 h22 kb_1732_225
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 254 2 h23 kb_1732_254
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 262 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 256 6 h24 kb_1732_256
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 262 2 h25 kb_1732_262
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 264 22 h26 kb_1732_264
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 286 3 h27 kb_1732_286
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 289 14 h28 kb_1732_289
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 303 40 h29 kb_1732_303
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 343 7 h30 kb_1732_343
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 350 6 h31 kb_1732_350
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 356 1 h32 kb_1732_356
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 357 14 h33 kb_1732_357
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 371 18 h34 kb_1732_371
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 389 6 h35 kb_1732_389
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 397 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 395 2 h36 kb_1732_395
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 397 22 h37 kb_1732_397
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 419 3 h38 kb_1732_419
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 422 15 h39 kb_1732_422
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 477 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 437 40 h40 kb_1732_437
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 498 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 477 21 h41 kb_1732_477
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 498 2 h42 kb_1732_498
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 500 19 h43 kb_1732_500
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 521 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 519 2 h44 kb_1732_519
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 521 3 h45 kb_1732_521
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 531 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 524 7 h46 kb_1732_524
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 531 17 h47 kb_1732_531
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 548 2 h48 kb_1732_548
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 550 11 h49 kb_1732_550
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 561 2 h50 kb_1732_561
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 563 1 h51 kb_1732_563
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 564 1 h52 kb_1732_564
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 565 2 h53 kb_1732_565
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 569 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 567 2 h54 kb_1732_567
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 569 3 h55 kb_1732_569
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 572 6 h56 kb_1732_572
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 581 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 578 3 h57 kb_1732_578
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 581 2 h58 kb_1732_581
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 583 3 h59 kb_1732_583
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 588 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 586 2 h60 kb_1732_586
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 590 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 588 2 h61 kb_1732_588
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 590 6 h62 kb_1732_590
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 596 1 h63 kb_1732_596
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 597 3 h64 kb_1732_597
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 600 1 h65 kb_1732_600
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 601 1 h66 kb_1732_601
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 612 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 602 10 h67 kb_1732_602
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 612 1 h68 kb_1732_612
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 613 3 h69 kb_1732_613
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 616 2 h70 kb_1732_616
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 621 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 618 3 h71 kb_1732_618
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 628 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 621 7 h72 kb_1732_621
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 630 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 628 2 h73 kb_1732_628
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 630 6 h74 kb_1732_630
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 636 3 h75 kb_1732_636
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 639 3 h76 kb_1732_639
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 647 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 642 5 h77 kb_1732_642
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 647 11 h78 kb_1732_647
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 658 2 h79 kb_1732_658
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 660 1 h80 kb_1732_660
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 661 9 h81 kb_1732_661
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 674 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 670 4 h82 kb_1732_670
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 674 1 h83 kb_1732_674
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 682 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 675 7 h84 kb_1732_675
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 682 2 h85 kb_1732_682
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 684 3 h86 kb_1732_684
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 687 4 h87 kb_1732_687
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 691 2 h88 kb_1732_691
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 702 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 693 9 h89 kb_1732_693
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 704 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 702 2 h90 kb_1732_702
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 704 2 h91 kb_1732_704
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 714 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 706 8 h92 kb_1732_706
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 717 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 714 3 h93 kb_1732_714
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 717 5 h94 kb_1732_717
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 722 10 h95 kb_1732_722
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 732 10 h96 kb_1732_732
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 742 14 h97 kb_1732_742
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 756 1 h98 kb_1732_756
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 775 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 757 18 h99 kb_1732_757
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 775 19 h100 kb_1732_775
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 794 34 h101 kb_1732_794
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 828 2 h102 kb_1732_828
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 836 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 830 6 h103 kb_1732_830
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 838 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 836 2 h104 kb_1732_836
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 860 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 838 22 h105 kb_1732_838
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 913 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 860 53 h106 kb_1732_860
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 917 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 913 4 h107 kb_1732_913
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 919 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 917 2 h108 kb_1732_917
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 919 8 h109 kb_1732_919
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 927 9 h110 kb_1732_927
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 939 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 936 3 h111 kb_1732_936
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 939 4 h112 kb_1732_939
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 947 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 943 4 h113 kb_1732_943
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 947 2 h114 kb_1732_947
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 958 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 949 9 h115 kb_1732_949
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 958 7 h116 kb_1732_958
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 966 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 965 1 h117 kb_1732_965
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 967 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 966 1 h118 kb_1732_966
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 968 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 967 1 h119 kb_1732_967
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 969 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 968 1 h120 kb_1732_968
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 970 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 969 1 h121 kb_1732_969
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 970 2 h122 kb_1732_970
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 973 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 972 1 h123 kb_1732_972
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 973 1 h124 kb_1732_973
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 975 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 974 1 h125 kb_1732_974
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 976 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 975 1 h126 kb_1732_975
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 976 2 h127 kb_1732_976
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 979 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 978 1 h128 kb_1732_978
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 980 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 979 1 h129 kb_1732_979
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 982 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 980 2 h130 kb_1732_980
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 983 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 982 1 h131 kb_1732_982
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 984 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 983 1 h132 kb_1732_983
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 985 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 984 1 h133 kb_1732_984
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 987 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 985 2 h134 kb_1732_985
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 989 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 987 2 h135 kb_1732_987
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 989 2 h136 kb_1732_989
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 992 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 991 1 h137 kb_1732_991
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 994 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 992 2 h138 kb_1732_992
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 995 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 994 1 h139 kb_1732_994
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 997 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 995 2 h140 kb_1732_995
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1001 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 997 4 h141 kb_1732_997
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1003 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1001 2 h142 kb_1732_1001
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1004 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1003 1 h143 kb_1732_1003
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1004 1 h144 kb_1732_1004
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1007 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1005 2 h145 kb_1732_1005
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1009 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1007 2 h146 kb_1732_1007
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1011 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1009 2 h147 kb_1732_1009
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1012 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1011 1 h148 kb_1732_1011
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1014 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1012 2 h149 kb_1732_1012
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1017 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1014 3 h150 kb_1732_1014
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1019 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1017 2 h151 kb_1732_1017
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1019 3 h152 kb_1732_1019
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1024 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1022 2 h153 kb_1732_1022
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1025 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1024 1 h154 kb_1732_1024
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1026 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1025 1 h155 kb_1732_1025
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1027 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1026 1 h156 kb_1732_1026
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1027 1 h157 kb_1732_1027
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1029 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1028 1 h158 kb_1732_1028
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1030 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1029 1 h159 kb_1732_1029
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1032 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1030 2 h160 kb_1732_1030
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1033 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1032 1 h161 kb_1732_1032
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1034 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1033 1 h162 kb_1732_1033
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1037 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1034 3 h163 kb_1732_1034
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1066 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1037 29 h164 kb_1732_1037
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1066 2 h165 kb_1732_1066
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1074 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1068 6 h166 kb_1732_1068
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1076 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1074 2 h167 kb_1732_1074
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1098 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1076 22 h168 kb_1732_1076
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1098 38 h169 kb_1732_1098
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1136 20 h170 kb_1732_1136
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1156 10 h171 kb_1732_1156
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1166 1 h172 kb_1732_1166
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1167 9 h173 kb_1732_1167
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1176 2 h174 kb_1732_1176
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1178 6 h175 kb_1732_1178
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1184 1 h176 kb_1732_1184
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1185 3 h177 kb_1732_1185
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1188 1 h178 kb_1732_1188
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1189 3 h179 kb_1732_1189
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1192 1 h180 kb_1732_1192
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1193 2 h181 kb_1732_1193
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1195 1 h182 kb_1732_1195
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1196 29 h183 kb_1732_1196
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1225 2 h184 kb_1732_1225
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1227 6 h185 kb_1732_1227
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1233 2 h186 kb_1732_1233
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1235 22 h187 kb_1732_1235
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1257 51 h188 kb_1732_1257
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1308 13 h189 kb_1732_1308
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1321 12 h190 kb_1732_1321
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1333 30 h191 kb_1732_1333
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1363 3 h192 kb_1732_1363
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1366 2 h193 kb_1732_1366
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1368 1 h194 kb_1732_1368
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1369 3 h195 kb_1732_1369
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1372 11 h196 kb_1732_1372
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1383 16 h197 kb_1732_1383
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1399 9 h198 kb_1732_1399
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1408 1 h199 kb_1732_1408
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1409 2 h200 kb_1732_1409
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1411 2 h201 kb_1732_1411
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1414 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1413 1 h202 kb_1732_1413
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1414 2 h203 kb_1732_1414
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1416 2 h204 kb_1732_1416
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1418 2 h205 kb_1732_1418
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1422 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1420 2 h206 kb_1732_1420
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1422 2 h207 kb_1732_1422
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1424 1 h208 kb_1732_1424
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1426 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1425 1 h209 kb_1732_1425
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1426 2 h210 kb_1732_1426
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1428 1 h211 kb_1732_1428
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1429 1 h212 kb_1732_1429
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1430 1 h213 kb_1732_1430
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1433 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1431 2 h214 kb_1732_1431
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1433 1 h215 kb_1732_1433
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1435 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1434 1 h216 kb_1732_1434
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1435 1 h217 kb_1732_1435
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1436 1 h218 kb_1732_1436
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1441 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1437 4 h219 kb_1732_1437
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1441 5 h220 kb_1732_1441
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1446 1 h221 kb_1732_1446
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1447 1 h222 kb_1732_1447
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1448 2 h223 kb_1732_1448
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1450 1 h224 kb_1732_1450
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1452 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1451 1 h225 kb_1732_1451
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1452 2 h226 kb_1732_1452
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1456 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1454 2 h227 kb_1732_1454
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1456 1 h228 kb_1732_1456
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1462 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1457 5 h229 kb_1732_1457
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1462 1 h230 kb_1732_1462
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1463 1 h231 kb_1732_1463
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1464 1 h232 kb_1732_1464
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1465 4 h233 kb_1732_1465
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1469 3 h234 kb_1732_1469
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1472 4 h235 kb_1732_1472
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1484 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1476 8 h236 kb_1732_1476
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1484 2 h237 kb_1732_1484
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1486 2 h238 kb_1732_1486
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1490 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1488 2 h239 kb_1732_1488
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1490 2 h240 kb_1732_1490
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1492 3 h241 kb_1732_1492
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1498 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1495 3 h242 kb_1732_1495
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1732.lits.getD i 0)) 0 1498 2 h243 kb_1732_1498
    exact h244
  have hg : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1500 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 4 = true := kg_1732_0
    have h1 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 9 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 4 5 h0 kg_1732_4
    have h2 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 10 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 9 1 h1 kg_1732_9
    have h3 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 27 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 10 17 h2 kg_1732_10
    have h4 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 32 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 27 5 h3 kg_1732_27
    have h5 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 33 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 32 1 h4 kg_1732_32
    have h6 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 44 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 33 11 h5 kg_1732_33
    have h7 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 45 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 44 1 h6 kg_1732_44
    have h8 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 62 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 45 17 h7 kg_1732_45
    have h9 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 72 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 62 10 h8 kg_1732_62
    have h10 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 73 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 72 1 h9 kg_1732_72
    have h11 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 82 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 73 9 h10 kg_1732_73
    have h12 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 180 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 82 98 h11 kg_1732_82
    have h13 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 196 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 180 16 h12 kg_1732_180
    have h14 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 198 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 196 2 h13 kg_1732_196
    have h15 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 200 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 198 2 h14 kg_1732_198
    have h16 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 203 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 200 3 h15 kg_1732_200
    have h17 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 211 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 203 8 h16 kg_1732_203
    have h18 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 215 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 211 4 h17 kg_1732_211
    have h19 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 217 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 215 2 h18 kg_1732_215
    have h20 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 223 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 217 6 h19 kg_1732_217
    have h21 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 224 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 223 1 h20 kg_1732_223
    have h22 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 225 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 224 1 h21 kg_1732_224
    have h23 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 254 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 225 29 h22 kg_1732_225
    have h24 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 256 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 254 2 h23 kg_1732_254
    have h25 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 262 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 256 6 h24 kg_1732_256
    have h26 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 264 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 262 2 h25 kg_1732_262
    have h27 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 286 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 264 22 h26 kg_1732_264
    have h28 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 289 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 286 3 h27 kg_1732_286
    have h29 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 303 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 289 14 h28 kg_1732_289
    have h30 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 343 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 303 40 h29 kg_1732_303
    have h31 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 350 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 343 7 h30 kg_1732_343
    have h32 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 356 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 350 6 h31 kg_1732_350
    have h33 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 357 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 356 1 h32 kg_1732_356
    have h34 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 371 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 357 14 h33 kg_1732_357
    have h35 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 389 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 371 18 h34 kg_1732_371
    have h36 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 395 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 389 6 h35 kg_1732_389
    have h37 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 397 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 395 2 h36 kg_1732_395
    have h38 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 419 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 397 22 h37 kg_1732_397
    have h39 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 422 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 419 3 h38 kg_1732_419
    have h40 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 437 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 422 15 h39 kg_1732_422
    have h41 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 477 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 437 40 h40 kg_1732_437
    have h42 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 498 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 477 21 h41 kg_1732_477
    have h43 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 500 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 498 2 h42 kg_1732_498
    have h44 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 519 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 500 19 h43 kg_1732_500
    have h45 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 521 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 519 2 h44 kg_1732_519
    have h46 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 524 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 521 3 h45 kg_1732_521
    have h47 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 531 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 524 7 h46 kg_1732_524
    have h48 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 548 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 531 17 h47 kg_1732_531
    have h49 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 550 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 548 2 h48 kg_1732_548
    have h50 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 561 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 550 11 h49 kg_1732_550
    have h51 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 563 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 561 2 h50 kg_1732_561
    have h52 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 564 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 563 1 h51 kg_1732_563
    have h53 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 565 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 564 1 h52 kg_1732_564
    have h54 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 567 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 565 2 h53 kg_1732_565
    have h55 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 569 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 567 2 h54 kg_1732_567
    have h56 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 572 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 569 3 h55 kg_1732_569
    have h57 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 578 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 572 6 h56 kg_1732_572
    have h58 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 581 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 578 3 h57 kg_1732_578
    have h59 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 583 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 581 2 h58 kg_1732_581
    have h60 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 586 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 583 3 h59 kg_1732_583
    have h61 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 588 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 586 2 h60 kg_1732_586
    have h62 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 590 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 588 2 h61 kg_1732_588
    have h63 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 596 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 590 6 h62 kg_1732_590
    have h64 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 597 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 596 1 h63 kg_1732_596
    have h65 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 600 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 597 3 h64 kg_1732_597
    have h66 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 601 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 600 1 h65 kg_1732_600
    have h67 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 602 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 601 1 h66 kg_1732_601
    have h68 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 612 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 602 10 h67 kg_1732_602
    have h69 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 613 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 612 1 h68 kg_1732_612
    have h70 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 616 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 613 3 h69 kg_1732_613
    have h71 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 618 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 616 2 h70 kg_1732_616
    have h72 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 621 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 618 3 h71 kg_1732_618
    have h73 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 628 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 621 7 h72 kg_1732_621
    have h74 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 630 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 628 2 h73 kg_1732_628
    have h75 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 636 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 630 6 h74 kg_1732_630
    have h76 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 639 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 636 3 h75 kg_1732_636
    have h77 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 642 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 639 3 h76 kg_1732_639
    have h78 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 647 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 642 5 h77 kg_1732_642
    have h79 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 658 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 647 11 h78 kg_1732_647
    have h80 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 660 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 658 2 h79 kg_1732_658
    have h81 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 661 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 660 1 h80 kg_1732_660
    have h82 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 670 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 661 9 h81 kg_1732_661
    have h83 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 674 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 670 4 h82 kg_1732_670
    have h84 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 675 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 674 1 h83 kg_1732_674
    have h85 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 682 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 675 7 h84 kg_1732_675
    have h86 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 684 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 682 2 h85 kg_1732_682
    have h87 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 687 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 684 3 h86 kg_1732_684
    have h88 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 691 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 687 4 h87 kg_1732_687
    have h89 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 693 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 691 2 h88 kg_1732_691
    have h90 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 702 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 693 9 h89 kg_1732_693
    have h91 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 704 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 702 2 h90 kg_1732_702
    have h92 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 706 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 704 2 h91 kg_1732_704
    have h93 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 714 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 706 8 h92 kg_1732_706
    have h94 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 717 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 714 3 h93 kg_1732_714
    have h95 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 722 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 717 5 h94 kg_1732_717
    have h96 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 732 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 722 10 h95 kg_1732_722
    have h97 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 742 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 732 10 h96 kg_1732_732
    have h98 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 756 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 742 14 h97 kg_1732_742
    have h99 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 757 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 756 1 h98 kg_1732_756
    have h100 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 775 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 757 18 h99 kg_1732_757
    have h101 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 794 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 775 19 h100 kg_1732_775
    have h102 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 828 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 794 34 h101 kg_1732_794
    have h103 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 830 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 828 2 h102 kg_1732_828
    have h104 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 836 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 830 6 h103 kg_1732_830
    have h105 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 838 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 836 2 h104 kg_1732_836
    have h106 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 860 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 838 22 h105 kg_1732_838
    have h107 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 913 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 860 53 h106 kg_1732_860
    have h108 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 917 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 913 4 h107 kg_1732_913
    have h109 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 919 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 917 2 h108 kg_1732_917
    have h110 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 927 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 919 8 h109 kg_1732_919
    have h111 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 936 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 927 9 h110 kg_1732_927
    have h112 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 939 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 936 3 h111 kg_1732_936
    have h113 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 943 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 939 4 h112 kg_1732_939
    have h114 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 947 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 943 4 h113 kg_1732_943
    have h115 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 949 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 947 2 h114 kg_1732_947
    have h116 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 958 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 949 9 h115 kg_1732_949
    have h117 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 965 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 958 7 h116 kg_1732_958
    have h118 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 966 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 965 1 h117 kg_1732_965
    have h119 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 967 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 966 1 h118 kg_1732_966
    have h120 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 968 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 967 1 h119 kg_1732_967
    have h121 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 969 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 968 1 h120 kg_1732_968
    have h122 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 970 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 969 1 h121 kg_1732_969
    have h123 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 972 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 970 2 h122 kg_1732_970
    have h124 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 973 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 972 1 h123 kg_1732_972
    have h125 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 974 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 973 1 h124 kg_1732_973
    have h126 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 975 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 974 1 h125 kg_1732_974
    have h127 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 976 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 975 1 h126 kg_1732_975
    have h128 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 978 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 976 2 h127 kg_1732_976
    have h129 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 979 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 978 1 h128 kg_1732_978
    have h130 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 980 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 979 1 h129 kg_1732_979
    have h131 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 982 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 980 2 h130 kg_1732_980
    have h132 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 983 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 982 1 h131 kg_1732_982
    have h133 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 984 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 983 1 h132 kg_1732_983
    have h134 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 985 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 984 1 h133 kg_1732_984
    have h135 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 987 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 985 2 h134 kg_1732_985
    have h136 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 989 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 987 2 h135 kg_1732_987
    have h137 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 991 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 989 2 h136 kg_1732_989
    have h138 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 992 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 991 1 h137 kg_1732_991
    have h139 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 994 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 992 2 h138 kg_1732_992
    have h140 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 995 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 994 1 h139 kg_1732_994
    have h141 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 997 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 995 2 h140 kg_1732_995
    have h142 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1001 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 997 4 h141 kg_1732_997
    have h143 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1003 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1001 2 h142 kg_1732_1001
    have h144 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1004 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1003 1 h143 kg_1732_1003
    have h145 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1005 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1004 1 h144 kg_1732_1004
    have h146 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1007 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1005 2 h145 kg_1732_1005
    have h147 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1009 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1007 2 h146 kg_1732_1007
    have h148 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1011 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1009 2 h147 kg_1732_1009
    have h149 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1012 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1011 1 h148 kg_1732_1011
    have h150 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1014 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1012 2 h149 kg_1732_1012
    have h151 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1017 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1014 3 h150 kg_1732_1014
    have h152 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1019 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1017 2 h151 kg_1732_1017
    have h153 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1022 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1019 3 h152 kg_1732_1019
    have h154 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1024 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1022 2 h153 kg_1732_1022
    have h155 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1025 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1024 1 h154 kg_1732_1024
    have h156 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1026 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1025 1 h155 kg_1732_1025
    have h157 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1027 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1026 1 h156 kg_1732_1026
    have h158 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1028 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1027 1 h157 kg_1732_1027
    have h159 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1029 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1028 1 h158 kg_1732_1028
    have h160 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1030 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1029 1 h159 kg_1732_1029
    have h161 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1032 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1030 2 h160 kg_1732_1030
    have h162 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1033 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1032 1 h161 kg_1732_1032
    have h163 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1034 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1033 1 h162 kg_1732_1033
    have h164 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1037 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1034 3 h163 kg_1732_1034
    have h165 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1066 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1037 29 h164 kg_1732_1037
    have h166 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1068 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1066 2 h165 kg_1732_1066
    have h167 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1074 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1068 6 h166 kg_1732_1068
    have h168 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1076 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1074 2 h167 kg_1732_1074
    have h169 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1098 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1076 22 h168 kg_1732_1076
    have h170 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1136 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1098 38 h169 kg_1732_1098
    have h171 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1156 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1136 20 h170 kg_1732_1136
    have h172 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1166 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1156 10 h171 kg_1732_1156
    have h173 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1167 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1166 1 h172 kg_1732_1166
    have h174 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1176 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1167 9 h173 kg_1732_1167
    have h175 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1178 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1176 2 h174 kg_1732_1176
    have h176 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1184 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1178 6 h175 kg_1732_1178
    have h177 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1185 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1184 1 h176 kg_1732_1184
    have h178 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1188 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1185 3 h177 kg_1732_1185
    have h179 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1189 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1188 1 h178 kg_1732_1188
    have h180 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1192 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1189 3 h179 kg_1732_1189
    have h181 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1193 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1192 1 h180 kg_1732_1192
    have h182 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1195 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1193 2 h181 kg_1732_1193
    have h183 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1196 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1195 1 h182 kg_1732_1195
    have h184 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1225 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1196 29 h183 kg_1732_1196
    have h185 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1227 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1225 2 h184 kg_1732_1225
    have h186 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1233 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1227 6 h185 kg_1732_1227
    have h187 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1235 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1233 2 h186 kg_1732_1233
    have h188 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1257 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1235 22 h187 kg_1732_1235
    have h189 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1308 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1257 51 h188 kg_1732_1257
    have h190 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1321 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1308 13 h189 kg_1732_1308
    have h191 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1333 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1321 12 h190 kg_1732_1321
    have h192 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1363 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1333 30 h191 kg_1732_1333
    have h193 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1366 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1363 3 h192 kg_1732_1363
    have h194 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1368 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1366 2 h193 kg_1732_1366
    have h195 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1369 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1368 1 h194 kg_1732_1368
    have h196 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1372 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1369 3 h195 kg_1732_1369
    have h197 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1383 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1372 11 h196 kg_1732_1372
    have h198 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1399 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1383 16 h197 kg_1732_1383
    have h199 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1408 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1399 9 h198 kg_1732_1399
    have h200 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1409 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1408 1 h199 kg_1732_1408
    have h201 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1411 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1409 2 h200 kg_1732_1409
    have h202 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1413 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1411 2 h201 kg_1732_1411
    have h203 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1414 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1413 1 h202 kg_1732_1413
    have h204 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1416 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1414 2 h203 kg_1732_1414
    have h205 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1418 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1416 2 h204 kg_1732_1416
    have h206 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1420 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1418 2 h205 kg_1732_1418
    have h207 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1422 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1420 2 h206 kg_1732_1420
    have h208 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1424 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1422 2 h207 kg_1732_1422
    have h209 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1425 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1424 1 h208 kg_1732_1424
    have h210 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1426 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1425 1 h209 kg_1732_1425
    have h211 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1428 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1426 2 h210 kg_1732_1426
    have h212 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1429 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1428 1 h211 kg_1732_1428
    have h213 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1430 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1429 1 h212 kg_1732_1429
    have h214 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1431 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1430 1 h213 kg_1732_1430
    have h215 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1433 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1431 2 h214 kg_1732_1431
    have h216 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1434 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1433 1 h215 kg_1732_1433
    have h217 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1435 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1434 1 h216 kg_1732_1434
    have h218 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1436 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1435 1 h217 kg_1732_1435
    have h219 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1437 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1436 1 h218 kg_1732_1436
    have h220 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1441 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1437 4 h219 kg_1732_1437
    have h221 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1446 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1441 5 h220 kg_1732_1441
    have h222 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1447 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1446 1 h221 kg_1732_1446
    have h223 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1448 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1447 1 h222 kg_1732_1447
    have h224 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1450 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1448 2 h223 kg_1732_1448
    have h225 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1451 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1450 1 h224 kg_1732_1450
    have h226 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1452 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1451 1 h225 kg_1732_1451
    have h227 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1454 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1452 2 h226 kg_1732_1452
    have h228 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1456 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1454 2 h227 kg_1732_1454
    have h229 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1457 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1456 1 h228 kg_1732_1456
    have h230 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1462 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1457 5 h229 kg_1732_1457
    have h231 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1463 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1462 1 h230 kg_1732_1462
    have h232 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1464 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1463 1 h231 kg_1732_1463
    have h233 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1465 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1464 1 h232 kg_1732_1464
    have h234 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1469 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1465 4 h233 kg_1732_1465
    have h235 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1472 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1469 3 h234 kg_1732_1469
    have h236 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1476 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1472 4 h235 kg_1732_1472
    have h237 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1484 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1476 8 h236 kg_1732_1476
    have h238 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1486 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1484 2 h237 kg_1732_1484
    have h239 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1488 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1486 2 h238 kg_1732_1486
    have h240 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1490 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1488 2 h239 kg_1732_1488
    have h241 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1492 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1490 2 h240 kg_1732_1490
    have h242 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1495 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1492 3 h241 kg_1732_1492
    have h243 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1498 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1495 3 h242 kg_1732_1495
    have h244 : IPChk.allR (Pts.glueIB K1732.lits KW_1732) 0 1500 = true := IPChk.allR_join (Pts.glueIB K1732.lits KW_1732) 0 1498 2 h243 kg_1732_1498
    exact h244
  have hlen : K1732.lits.length = 1500 := by decide
  intro k h1 h2
  obtain rfl : k = 1732 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1732) K1732.lits KW_1732
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_338 : ∀ k, 1733 ≤ k → k < 1734 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1733 JW_1733 1733 1 jr_1733
theorem jr6_339 : ∀ k, 1734 ≤ k → k < 1735 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 520 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 7 = true := kb_1734_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 7 12 h0 kb_1734_7
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 19 5 h1 kb_1734_19
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 24 9 h2 kb_1734_24
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 33 11 h3 kb_1734_33
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 44 1 h4 kb_1734_44
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 45 1 h5 kb_1734_45
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 46 35 h6 kb_1734_46
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 81 6 h7 kb_1734_81
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 87 1 h8 kb_1734_87
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 88 2 h9 kb_1734_88
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 90 4 h10 kb_1734_90
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 94 5 h11 kb_1734_94
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 99 3 h12 kb_1734_99
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 102 22 h13 kb_1734_102
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 124 2 h14 kb_1734_124
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 126 31 h15 kb_1734_126
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 157 1 h16 kb_1734_157
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 158 9 h17 kb_1734_158
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 167 7 h18 kb_1734_167
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 174 8 h19 kb_1734_174
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 182 17 h20 kb_1734_182
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 199 2 h21 kb_1734_199
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 201 12 h22 kb_1734_201
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 213 2 h23 kb_1734_213
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 215 1 h24 kb_1734_215
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 216 14 h25 kb_1734_216
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 230 26 h26 kb_1734_230
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 256 19 h27 kb_1734_256
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 275 28 h28 kb_1734_275
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 303 29 h29 kb_1734_303
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 332 2 h30 kb_1734_332
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 334 6 h31 kb_1734_334
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 340 5 h32 kb_1734_340
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 345 76 h33 kb_1734_345
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 421 18 h34 kb_1734_421
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 457 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 439 18 h35 kb_1734_439
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 457 40 h36 kb_1734_457
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 497 2 h37 kb_1734_497
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 499 8 h38 kb_1734_499
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1734.lits.getD i 0)) 0 507 13 h39 kb_1734_507
    exact h40
  have hg : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 520 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 7 = true := kg_1734_0
    have h1 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 19 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 7 12 h0 kg_1734_7
    have h2 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 24 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 19 5 h1 kg_1734_19
    have h3 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 33 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 24 9 h2 kg_1734_24
    have h4 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 44 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 33 11 h3 kg_1734_33
    have h5 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 45 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 44 1 h4 kg_1734_44
    have h6 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 46 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 45 1 h5 kg_1734_45
    have h7 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 81 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 46 35 h6 kg_1734_46
    have h8 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 87 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 81 6 h7 kg_1734_81
    have h9 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 88 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 87 1 h8 kg_1734_87
    have h10 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 90 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 88 2 h9 kg_1734_88
    have h11 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 94 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 90 4 h10 kg_1734_90
    have h12 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 99 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 94 5 h11 kg_1734_94
    have h13 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 102 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 99 3 h12 kg_1734_99
    have h14 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 124 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 102 22 h13 kg_1734_102
    have h15 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 126 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 124 2 h14 kg_1734_124
    have h16 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 157 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 126 31 h15 kg_1734_126
    have h17 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 158 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 157 1 h16 kg_1734_157
    have h18 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 167 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 158 9 h17 kg_1734_158
    have h19 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 174 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 167 7 h18 kg_1734_167
    have h20 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 182 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 174 8 h19 kg_1734_174
    have h21 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 199 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 182 17 h20 kg_1734_182
    have h22 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 201 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 199 2 h21 kg_1734_199
    have h23 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 213 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 201 12 h22 kg_1734_201
    have h24 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 215 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 213 2 h23 kg_1734_213
    have h25 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 216 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 215 1 h24 kg_1734_215
    have h26 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 230 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 216 14 h25 kg_1734_216
    have h27 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 256 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 230 26 h26 kg_1734_230
    have h28 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 275 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 256 19 h27 kg_1734_256
    have h29 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 303 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 275 28 h28 kg_1734_275
    have h30 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 332 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 303 29 h29 kg_1734_303
    have h31 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 334 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 332 2 h30 kg_1734_332
    have h32 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 340 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 334 6 h31 kg_1734_334
    have h33 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 345 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 340 5 h32 kg_1734_340
    have h34 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 421 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 345 76 h33 kg_1734_345
    have h35 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 439 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 421 18 h34 kg_1734_421
    have h36 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 457 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 439 18 h35 kg_1734_439
    have h37 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 497 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 457 40 h36 kg_1734_457
    have h38 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 499 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 497 2 h37 kg_1734_497
    have h39 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 507 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 499 8 h38 kg_1734_499
    have h40 : IPChk.allR (Pts.glueIB K1734.lits KW_1734) 0 520 = true := IPChk.allR_join (Pts.glueIB K1734.lits KW_1734) 0 507 13 h39 kg_1734_507
    exact h40
  have hlen : K1734.lits.length = 520 := by decide
  intro k h1 h2
  obtain rfl : k = 1734 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1734) K1734.lits KW_1734
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_340 : ∀ k, 1735 ≤ k → k < 1738 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1735 JW_1735 1735 3 jr_1735
theorem jr6_341 : ∀ k, 1738 ≤ k → k < 1739 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 108 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 2 = true := kb_1738_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 2 28 h0 kb_1738_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 30 16 h1 kb_1738_30
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 46 28 h2 kb_1738_46
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 74 6 h3 kb_1738_74
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1738.lits.getD i 0)) 0 80 28 h4 kb_1738_80
    exact h5
  have hg : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 108 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 2 = true := kg_1738_0
    have h1 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 30 = true := IPChk.allR_join (Pts.glueIB K1738.lits KW_1738) 0 2 28 h0 kg_1738_2
    have h2 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 46 = true := IPChk.allR_join (Pts.glueIB K1738.lits KW_1738) 0 30 16 h1 kg_1738_30
    have h3 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 74 = true := IPChk.allR_join (Pts.glueIB K1738.lits KW_1738) 0 46 28 h2 kg_1738_46
    have h4 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 80 = true := IPChk.allR_join (Pts.glueIB K1738.lits KW_1738) 0 74 6 h3 kg_1738_74
    have h5 : IPChk.allR (Pts.glueIB K1738.lits KW_1738) 0 108 = true := IPChk.allR_join (Pts.glueIB K1738.lits KW_1738) 0 80 28 h4 kg_1738_80
    exact h5
  have hlen : K1738.lits.length = 108 := by decide
  intro k h1 h2
  obtain rfl : k = 1738 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1738) K1738.lits KW_1738
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_342 : ∀ k, 1739 ≤ k → k < 1778 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1739 JW_1739 1739 39 jr_1739
theorem jr6_343 : ∀ k, 1778 ≤ k → k < 1779 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 801 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 5 = true := kb_1778_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 5 16 h0 kb_1778_5
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 21 14 h1 kb_1778_21
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 35 13 h2 kb_1778_35
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 48 1 h3 kb_1778_48
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 49 1 h4 kb_1778_49
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 50 17 h5 kb_1778_50
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 67 38 h6 kb_1778_67
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 105 1 h7 kb_1778_105
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 106 18 h8 kb_1778_106
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 124 2 h9 kb_1778_124
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 126 6 h10 kb_1778_126
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 132 2 h11 kb_1778_132
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 134 19 h12 kb_1778_134
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 153 2 h13 kb_1778_153
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 155 1 h14 kb_1778_155
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 156 17 h15 kb_1778_156
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 173 2 h16 kb_1778_173
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 175 4 h17 kb_1778_175
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 179 2 h18 kb_1778_179
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 181 10 h19 kb_1778_181
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 191 2 h20 kb_1778_191
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 193 3 h21 kb_1778_193
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 196 1 h22 kb_1778_196
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 197 11 h23 kb_1778_197
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 208 5 h24 kb_1778_208
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 213 10 h25 kb_1778_213
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 223 15 h26 kb_1778_223
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 238 2 h27 kb_1778_238
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 240 13 h28 kb_1778_240
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 253 29 h29 kb_1778_253
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 290 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 282 8 h30 kb_1778_282
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 317 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 290 27 h31 kb_1778_290
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 317 3 h32 kb_1778_317
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 320 12 h33 kb_1778_320
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 332 5 h34 kb_1778_332
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 337 17 h35 kb_1778_337
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 354 29 h36 kb_1778_354
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 383 16 h37 kb_1778_383
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 399 4 h38 kb_1778_399
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 403 7 h39 kb_1778_403
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 410 11 h40 kb_1778_410
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 421 11 h41 kb_1778_421
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 441 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 432 9 h42 kb_1778_432
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 441 9 h43 kb_1778_441
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 450 13 h44 kb_1778_450
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 490 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 463 27 h45 kb_1778_463
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 490 1 h46 kb_1778_490
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 491 20 h47 kb_1778_491
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 511 7 h48 kb_1778_511
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 530 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 518 12 h49 kb_1778_518
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 530 10 h50 kb_1778_530
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 540 23 h51 kb_1778_540
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 563 10 h52 kb_1778_563
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 573 23 h53 kb_1778_573
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 599 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 596 3 h54 kb_1778_596
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 601 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 599 2 h55 kb_1778_599
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 601 6 h56 kb_1778_601
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 607 11 h57 kb_1778_607
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 618 18 h58 kb_1778_618
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 636 30 h59 kb_1778_636
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 679 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 666 13 h60 kb_1778_666
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 679 2 h61 kb_1778_679
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 681 4 h62 kb_1778_681
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 685 8 h63 kb_1778_685
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 712 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 693 19 h64 kb_1778_693
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 712 23 h65 kb_1778_712
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 765 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 735 30 h66 kb_1778_735
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 801 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1778.lits.getD i 0)) 0 765 36 h67 kb_1778_765
    exact h68
  have hg : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 801 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 5 = true := kg_1778_0
    have h1 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 21 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 5 16 h0 kg_1778_5
    have h2 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 35 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 21 14 h1 kg_1778_21
    have h3 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 48 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 35 13 h2 kg_1778_35
    have h4 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 49 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 48 1 h3 kg_1778_48
    have h5 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 50 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 49 1 h4 kg_1778_49
    have h6 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 67 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 50 17 h5 kg_1778_50
    have h7 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 105 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 67 38 h6 kg_1778_67
    have h8 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 106 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 105 1 h7 kg_1778_105
    have h9 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 124 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 106 18 h8 kg_1778_106
    have h10 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 126 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 124 2 h9 kg_1778_124
    have h11 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 132 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 126 6 h10 kg_1778_126
    have h12 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 134 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 132 2 h11 kg_1778_132
    have h13 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 153 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 134 19 h12 kg_1778_134
    have h14 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 155 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 153 2 h13 kg_1778_153
    have h15 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 156 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 155 1 h14 kg_1778_155
    have h16 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 173 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 156 17 h15 kg_1778_156
    have h17 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 175 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 173 2 h16 kg_1778_173
    have h18 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 179 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 175 4 h17 kg_1778_175
    have h19 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 181 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 179 2 h18 kg_1778_179
    have h20 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 191 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 181 10 h19 kg_1778_181
    have h21 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 193 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 191 2 h20 kg_1778_191
    have h22 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 196 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 193 3 h21 kg_1778_193
    have h23 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 197 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 196 1 h22 kg_1778_196
    have h24 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 208 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 197 11 h23 kg_1778_197
    have h25 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 213 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 208 5 h24 kg_1778_208
    have h26 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 223 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 213 10 h25 kg_1778_213
    have h27 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 238 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 223 15 h26 kg_1778_223
    have h28 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 240 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 238 2 h27 kg_1778_238
    have h29 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 253 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 240 13 h28 kg_1778_240
    have h30 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 282 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 253 29 h29 kg_1778_253
    have h31 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 290 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 282 8 h30 kg_1778_282
    have h32 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 317 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 290 27 h31 kg_1778_290
    have h33 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 320 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 317 3 h32 kg_1778_317
    have h34 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 332 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 320 12 h33 kg_1778_320
    have h35 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 337 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 332 5 h34 kg_1778_332
    have h36 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 354 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 337 17 h35 kg_1778_337
    have h37 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 383 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 354 29 h36 kg_1778_354
    have h38 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 399 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 383 16 h37 kg_1778_383
    have h39 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 403 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 399 4 h38 kg_1778_399
    have h40 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 410 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 403 7 h39 kg_1778_403
    have h41 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 421 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 410 11 h40 kg_1778_410
    have h42 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 432 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 421 11 h41 kg_1778_421
    have h43 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 441 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 432 9 h42 kg_1778_432
    have h44 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 450 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 441 9 h43 kg_1778_441
    have h45 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 463 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 450 13 h44 kg_1778_450
    have h46 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 490 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 463 27 h45 kg_1778_463
    have h47 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 491 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 490 1 h46 kg_1778_490
    have h48 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 511 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 491 20 h47 kg_1778_491
    have h49 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 518 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 511 7 h48 kg_1778_511
    have h50 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 530 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 518 12 h49 kg_1778_518
    have h51 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 540 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 530 10 h50 kg_1778_530
    have h52 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 563 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 540 23 h51 kg_1778_540
    have h53 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 573 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 563 10 h52 kg_1778_563
    have h54 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 596 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 573 23 h53 kg_1778_573
    have h55 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 599 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 596 3 h54 kg_1778_596
    have h56 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 601 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 599 2 h55 kg_1778_599
    have h57 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 607 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 601 6 h56 kg_1778_601
    have h58 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 618 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 607 11 h57 kg_1778_607
    have h59 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 636 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 618 18 h58 kg_1778_618
    have h60 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 666 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 636 30 h59 kg_1778_636
    have h61 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 679 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 666 13 h60 kg_1778_666
    have h62 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 681 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 679 2 h61 kg_1778_679
    have h63 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 685 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 681 4 h62 kg_1778_681
    have h64 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 693 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 685 8 h63 kg_1778_685
    have h65 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 712 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 693 19 h64 kg_1778_693
    have h66 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 735 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 712 23 h65 kg_1778_712
    have h67 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 765 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 735 30 h66 kg_1778_735
    have h68 : IPChk.allR (Pts.glueIB K1778.lits KW_1778) 0 801 = true := IPChk.allR_join (Pts.glueIB K1778.lits KW_1778) 0 765 36 h67 kg_1778_765
    exact h68
  have hlen : K1778.lits.length = 801 := by decide
  intro k h1 h2
  obtain rfl : k = 1778 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1778) K1778.lits KW_1778
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_344 : ∀ k, 1779 ≤ k → k < 1780 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1779 JW_1779 1779 1 jr_1779
theorem jr6_345 : ∀ k, 1780 ≤ k → k < 1781 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 844 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 3 = true := kb_1780_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 3 16 h0 kb_1780_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 19 12 h1 kb_1780_19
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 31 1 h2 kb_1780_31
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 32 1 h3 kb_1780_32
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 33 18 h4 kb_1780_33
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 51 40 h5 kb_1780_51
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 91 18 h6 kb_1780_91
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 109 2 h7 kb_1780_109
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 111 6 h8 kb_1780_111
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 117 2 h9 kb_1780_117
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 119 17 h10 kb_1780_119
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 136 2 h11 kb_1780_136
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 138 12 h12 kb_1780_138
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 150 4 h13 kb_1780_150
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 154 11 h14 kb_1780_154
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 165 15 h15 kb_1780_165
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 180 2 h16 kb_1780_180
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 182 14 h17 kb_1780_182
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 196 15 h18 kb_1780_196
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 211 2 h19 kb_1780_211
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 213 14 h20 kb_1780_213
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 227 1 h21 kb_1780_227
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 228 7 h22 kb_1780_228
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 235 4 h23 kb_1780_235
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 239 16 h24 kb_1780_239
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 255 2 h25 kb_1780_255
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 257 12 h26 kb_1780_257
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 269 2 h27 kb_1780_269
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 277 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 271 6 h28 kb_1780_271
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 277 2 h29 kb_1780_277
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 279 13 h30 kb_1780_279
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 292 5 h31 kb_1780_292
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 297 5 h32 kb_1780_297
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 302 14 h33 kb_1780_302
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 316 23 h34 kb_1780_316
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 339 19 h35 kb_1780_339
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 358 2 h36 kb_1780_358
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 360 6 h37 kb_1780_360
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 366 2 h38 kb_1780_366
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 368 17 h39 kb_1780_368
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 385 2 h40 kb_1780_385
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 390 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 387 3 h41 kb_1780_387
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 390 6 h42 kb_1780_390
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 396 2 h43 kb_1780_396
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 398 18 h44 kb_1780_398
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 416 12 h45 kb_1780_416
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 440 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 428 12 h46 kb_1780_428
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 440 3 h47 kb_1780_440
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 451 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 443 8 h48 kb_1780_443
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 451 2 h49 kb_1780_451
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 453 16 h50 kb_1780_453
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 469 22 h51 kb_1780_469
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 491 4 h52 kb_1780_491
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 495 5 h53 kb_1780_495
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 500 2 h54 kb_1780_500
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 502 17 h55 kb_1780_502
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 539 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 519 20 h56 kb_1780_519
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 544 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 539 5 h57 kb_1780_539
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 546 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 544 2 h58 kb_1780_544
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 546 2 h59 kb_1780_546
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 548 5 h60 kb_1780_548
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 553 1 h61 kb_1780_553
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 562 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 554 8 h62 kb_1780_554
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 568 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 562 6 h63 kb_1780_562
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 569 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 568 1 h64 kb_1780_568
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 580 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 569 11 h65 kb_1780_569
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 580 11 h66 kb_1780_580
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 598 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 591 7 h67 kb_1780_591
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 598 8 h68 kb_1780_598
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 606 12 h69 kb_1780_606
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 621 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 618 3 h70 kb_1780_618
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 621 5 h71 kb_1780_621
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 628 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 626 2 h72 kb_1780_626
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 628 7 h73 kb_1780_628
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 635 4 h74 kb_1780_635
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 639 9 h75 kb_1780_639
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 648 4 h76 kb_1780_648
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 652 13 h77 kb_1780_652
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 665 12 h78 kb_1780_665
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 677 14 h79 kb_1780_677
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 691 10 h80 kb_1780_691
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 701 14 h81 kb_1780_701
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 715 20 h82 kb_1780_715
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 769 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 735 34 h83 kb_1780_735
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 769 33 h84 kb_1780_769
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 802 6 h85 kb_1780_802
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 810 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 808 2 h86 kb_1780_808
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 810 13 h87 kb_1780_810
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 823 6 h88 kb_1780_823
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1780.lits.getD i 0)) 0 829 15 h89 kb_1780_829
    exact h90
  have hg : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 844 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 3 = true := kg_1780_0
    have h1 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 19 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 3 16 h0 kg_1780_3
    have h2 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 31 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 19 12 h1 kg_1780_19
    have h3 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 32 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 31 1 h2 kg_1780_31
    have h4 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 33 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 32 1 h3 kg_1780_32
    have h5 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 51 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 33 18 h4 kg_1780_33
    have h6 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 91 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 51 40 h5 kg_1780_51
    have h7 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 109 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 91 18 h6 kg_1780_91
    have h8 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 111 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 109 2 h7 kg_1780_109
    have h9 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 117 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 111 6 h8 kg_1780_111
    have h10 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 119 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 117 2 h9 kg_1780_117
    have h11 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 136 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 119 17 h10 kg_1780_119
    have h12 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 138 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 136 2 h11 kg_1780_136
    have h13 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 150 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 138 12 h12 kg_1780_138
    have h14 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 154 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 150 4 h13 kg_1780_150
    have h15 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 165 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 154 11 h14 kg_1780_154
    have h16 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 180 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 165 15 h15 kg_1780_165
    have h17 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 182 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 180 2 h16 kg_1780_180
    have h18 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 196 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 182 14 h17 kg_1780_182
    have h19 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 211 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 196 15 h18 kg_1780_196
    have h20 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 213 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 211 2 h19 kg_1780_211
    have h21 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 227 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 213 14 h20 kg_1780_213
    have h22 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 228 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 227 1 h21 kg_1780_227
    have h23 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 235 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 228 7 h22 kg_1780_228
    have h24 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 239 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 235 4 h23 kg_1780_235
    have h25 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 255 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 239 16 h24 kg_1780_239
    have h26 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 257 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 255 2 h25 kg_1780_255
    have h27 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 269 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 257 12 h26 kg_1780_257
    have h28 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 271 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 269 2 h27 kg_1780_269
    have h29 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 277 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 271 6 h28 kg_1780_271
    have h30 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 279 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 277 2 h29 kg_1780_277
    have h31 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 292 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 279 13 h30 kg_1780_279
    have h32 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 297 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 292 5 h31 kg_1780_292
    have h33 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 302 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 297 5 h32 kg_1780_297
    have h34 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 316 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 302 14 h33 kg_1780_302
    have h35 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 339 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 316 23 h34 kg_1780_316
    have h36 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 358 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 339 19 h35 kg_1780_339
    have h37 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 360 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 358 2 h36 kg_1780_358
    have h38 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 366 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 360 6 h37 kg_1780_360
    have h39 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 368 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 366 2 h38 kg_1780_366
    have h40 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 385 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 368 17 h39 kg_1780_368
    have h41 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 387 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 385 2 h40 kg_1780_385
    have h42 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 390 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 387 3 h41 kg_1780_387
    have h43 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 396 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 390 6 h42 kg_1780_390
    have h44 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 398 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 396 2 h43 kg_1780_396
    have h45 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 416 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 398 18 h44 kg_1780_398
    have h46 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 428 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 416 12 h45 kg_1780_416
    have h47 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 440 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 428 12 h46 kg_1780_428
    have h48 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 443 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 440 3 h47 kg_1780_440
    have h49 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 451 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 443 8 h48 kg_1780_443
    have h50 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 453 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 451 2 h49 kg_1780_451
    have h51 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 469 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 453 16 h50 kg_1780_453
    have h52 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 491 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 469 22 h51 kg_1780_469
    have h53 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 495 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 491 4 h52 kg_1780_491
    have h54 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 500 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 495 5 h53 kg_1780_495
    have h55 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 502 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 500 2 h54 kg_1780_500
    have h56 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 519 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 502 17 h55 kg_1780_502
    have h57 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 539 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 519 20 h56 kg_1780_519
    have h58 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 544 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 539 5 h57 kg_1780_539
    have h59 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 546 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 544 2 h58 kg_1780_544
    have h60 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 548 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 546 2 h59 kg_1780_546
    have h61 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 553 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 548 5 h60 kg_1780_548
    have h62 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 554 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 553 1 h61 kg_1780_553
    have h63 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 562 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 554 8 h62 kg_1780_554
    have h64 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 568 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 562 6 h63 kg_1780_562
    have h65 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 569 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 568 1 h64 kg_1780_568
    have h66 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 580 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 569 11 h65 kg_1780_569
    have h67 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 591 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 580 11 h66 kg_1780_580
    have h68 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 598 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 591 7 h67 kg_1780_591
    have h69 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 606 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 598 8 h68 kg_1780_598
    have h70 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 618 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 606 12 h69 kg_1780_606
    have h71 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 621 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 618 3 h70 kg_1780_618
    have h72 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 626 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 621 5 h71 kg_1780_621
    have h73 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 628 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 626 2 h72 kg_1780_626
    have h74 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 635 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 628 7 h73 kg_1780_628
    have h75 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 639 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 635 4 h74 kg_1780_635
    have h76 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 648 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 639 9 h75 kg_1780_639
    have h77 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 652 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 648 4 h76 kg_1780_648
    have h78 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 665 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 652 13 h77 kg_1780_652
    have h79 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 677 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 665 12 h78 kg_1780_665
    have h80 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 691 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 677 14 h79 kg_1780_677
    have h81 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 701 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 691 10 h80 kg_1780_691
    have h82 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 715 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 701 14 h81 kg_1780_701
    have h83 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 735 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 715 20 h82 kg_1780_715
    have h84 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 769 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 735 34 h83 kg_1780_735
    have h85 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 802 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 769 33 h84 kg_1780_769
    have h86 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 808 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 802 6 h85 kg_1780_802
    have h87 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 810 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 808 2 h86 kg_1780_808
    have h88 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 823 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 810 13 h87 kg_1780_810
    have h89 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 829 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 823 6 h88 kg_1780_823
    have h90 : IPChk.allR (Pts.glueIB K1780.lits KW_1780) 0 844 = true := IPChk.allR_join (Pts.glueIB K1780.lits KW_1780) 0 829 15 h89 kg_1780_829
    exact h90
  have hlen : K1780.lits.length = 844 := by decide
  intro k h1 h2
  obtain rfl : k = 1780 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1780) K1780.lits KW_1780
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_346 : ∀ k, 1781 ≤ k → k < 1782 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1781 JW_1781 1781 1 jr_1781
theorem jr6_347 : ∀ k, 1782 ≤ k → k < 1783 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 694 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 2 = true := kb_1782_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 2 18 h0 kb_1782_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 20 2 h1 kb_1782_20
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 22 6 h2 kb_1782_22
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 28 2 h3 kb_1782_28
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 30 22 h4 kb_1782_30
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 52 5 h5 kb_1782_52
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 57 6 h6 kb_1782_57
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 63 10 h7 kb_1782_63
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 73 14 h8 kb_1782_73
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 87 14 h9 kb_1782_87
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 101 14 h10 kb_1782_101
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 115 2 h11 kb_1782_115
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 117 6 h12 kb_1782_117
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 123 2 h13 kb_1782_123
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 125 22 h14 kb_1782_125
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 147 2 h15 kb_1782_147
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 149 9 h16 kb_1782_149
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 158 22 h17 kb_1782_158
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 180 15 h18 kb_1782_180
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 195 19 h19 kb_1782_195
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 214 14 h20 kb_1782_214
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 228 14 h21 kb_1782_228
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 242 2 h22 kb_1782_242
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 244 6 h23 kb_1782_244
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 250 5 h24 kb_1782_250
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 255 24 h25 kb_1782_255
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 279 2 h26 kb_1782_279
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 281 22 h27 kb_1782_281
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 303 16 h28 kb_1782_303
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 319 16 h29 kb_1782_319
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 335 16 h30 kb_1782_335
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 351 10 h31 kb_1782_351
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 361 19 h32 kb_1782_361
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 380 2 h33 kb_1782_380
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 382 5 h34 kb_1782_382
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 387 2 h35 kb_1782_387
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 406 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 389 17 h36 kb_1782_389
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 406 28 h37 kb_1782_406
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 434 10 h38 kb_1782_434
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 444 2 h39 kb_1782_444
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 446 2 h40 kb_1782_446
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 448 2 h41 kb_1782_448
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 450 3 h42 kb_1782_450
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 453 13 h43 kb_1782_453
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 466 10 h44 kb_1782_466
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 476 41 h45 kb_1782_476
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 517 12 h46 kb_1782_517
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 529 18 h47 kb_1782_529
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 547 4 h48 kb_1782_547
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 583 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 551 32 h49 kb_1782_551
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 592 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 583 9 h50 kb_1782_583
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 592 28 h51 kb_1782_592
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 633 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 620 13 h52 kb_1782_620
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 633 33 h53 kb_1782_633
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 694 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1782.lits.getD i 0)) 0 666 28 h54 kb_1782_666
    exact h55
  have hg : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 694 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 2 = true := kg_1782_0
    have h1 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 20 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 2 18 h0 kg_1782_2
    have h2 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 22 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 20 2 h1 kg_1782_20
    have h3 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 28 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 22 6 h2 kg_1782_22
    have h4 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 30 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 28 2 h3 kg_1782_28
    have h5 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 52 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 30 22 h4 kg_1782_30
    have h6 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 57 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 52 5 h5 kg_1782_52
    have h7 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 63 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 57 6 h6 kg_1782_57
    have h8 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 73 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 63 10 h7 kg_1782_63
    have h9 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 87 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 73 14 h8 kg_1782_73
    have h10 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 101 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 87 14 h9 kg_1782_87
    have h11 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 115 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 101 14 h10 kg_1782_101
    have h12 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 117 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 115 2 h11 kg_1782_115
    have h13 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 123 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 117 6 h12 kg_1782_117
    have h14 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 125 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 123 2 h13 kg_1782_123
    have h15 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 147 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 125 22 h14 kg_1782_125
    have h16 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 149 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 147 2 h15 kg_1782_147
    have h17 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 158 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 149 9 h16 kg_1782_149
    have h18 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 180 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 158 22 h17 kg_1782_158
    have h19 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 195 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 180 15 h18 kg_1782_180
    have h20 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 214 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 195 19 h19 kg_1782_195
    have h21 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 228 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 214 14 h20 kg_1782_214
    have h22 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 242 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 228 14 h21 kg_1782_228
    have h23 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 244 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 242 2 h22 kg_1782_242
    have h24 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 250 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 244 6 h23 kg_1782_244
    have h25 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 255 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 250 5 h24 kg_1782_250
    have h26 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 279 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 255 24 h25 kg_1782_255
    have h27 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 281 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 279 2 h26 kg_1782_279
    have h28 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 303 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 281 22 h27 kg_1782_281
    have h29 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 319 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 303 16 h28 kg_1782_303
    have h30 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 335 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 319 16 h29 kg_1782_319
    have h31 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 351 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 335 16 h30 kg_1782_335
    have h32 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 361 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 351 10 h31 kg_1782_351
    have h33 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 380 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 361 19 h32 kg_1782_361
    have h34 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 382 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 380 2 h33 kg_1782_380
    have h35 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 387 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 382 5 h34 kg_1782_382
    have h36 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 389 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 387 2 h35 kg_1782_387
    have h37 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 406 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 389 17 h36 kg_1782_389
    have h38 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 434 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 406 28 h37 kg_1782_406
    have h39 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 444 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 434 10 h38 kg_1782_434
    have h40 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 446 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 444 2 h39 kg_1782_444
    have h41 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 448 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 446 2 h40 kg_1782_446
    have h42 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 450 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 448 2 h41 kg_1782_448
    have h43 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 453 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 450 3 h42 kg_1782_450
    have h44 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 466 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 453 13 h43 kg_1782_453
    have h45 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 476 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 466 10 h44 kg_1782_466
    have h46 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 517 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 476 41 h45 kg_1782_476
    have h47 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 529 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 517 12 h46 kg_1782_517
    have h48 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 547 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 529 18 h47 kg_1782_529
    have h49 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 551 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 547 4 h48 kg_1782_547
    have h50 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 583 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 551 32 h49 kg_1782_551
    have h51 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 592 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 583 9 h50 kg_1782_583
    have h52 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 620 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 592 28 h51 kg_1782_592
    have h53 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 633 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 620 13 h52 kg_1782_620
    have h54 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 666 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 633 33 h53 kg_1782_633
    have h55 : IPChk.allR (Pts.glueIB K1782.lits KW_1782) 0 694 = true := IPChk.allR_join (Pts.glueIB K1782.lits KW_1782) 0 666 28 h54 kg_1782_666
    exact h55
  have hlen : K1782.lits.length = 694 := by decide
  intro k h1 h2
  obtain rfl : k = 1782 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1782) K1782.lits KW_1782
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_348 : ∀ k, 1783 ≤ k → k < 1828 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1783 JW_1783 1783 45 jr_1783
theorem jr6_349 : ∀ k, 1828 ≤ k → k < 1829 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 368 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 1 = true := kb_1828_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 1 1 h0 kb_1828_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 2 7 h1 kb_1828_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 9 13 h2 kb_1828_9
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 22 4 h3 kb_1828_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 26 2 h4 kb_1828_26
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 28 12 h5 kb_1828_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 40 1 h6 kb_1828_40
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 41 2 h7 kb_1828_41
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 43 2 h8 kb_1828_43
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 45 3 h9 kb_1828_45
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 48 9 h10 kb_1828_48
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 57 4 h11 kb_1828_57
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 61 8 h12 kb_1828_61
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 69 11 h13 kb_1828_69
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 80 2 h14 kb_1828_80
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 82 10 h15 kb_1828_82
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 92 20 h16 kb_1828_92
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 112 11 h17 kb_1828_112
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 123 56 h18 kb_1828_123
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 179 7 h19 kb_1828_179
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 186 2 h20 kb_1828_186
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 188 1 h21 kb_1828_188
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 189 17 h22 kb_1828_189
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 206 6 h23 kb_1828_206
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 212 14 h24 kb_1828_212
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 226 31 h25 kb_1828_226
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 293 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 257 36 h26 kb_1828_257
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 325 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 293 32 h27 kb_1828_293
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1828.lits.getD i 0)) 0 325 43 h28 kb_1828_325
    exact h29
  have hg : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 368 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 1 = true := kg_1828_0
    have h1 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 2 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 1 1 h0 kg_1828_1
    have h2 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 9 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 2 7 h1 kg_1828_2
    have h3 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 22 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 9 13 h2 kg_1828_9
    have h4 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 26 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 22 4 h3 kg_1828_22
    have h5 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 28 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 26 2 h4 kg_1828_26
    have h6 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 40 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 28 12 h5 kg_1828_28
    have h7 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 41 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 40 1 h6 kg_1828_40
    have h8 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 43 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 41 2 h7 kg_1828_41
    have h9 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 45 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 43 2 h8 kg_1828_43
    have h10 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 48 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 45 3 h9 kg_1828_45
    have h11 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 57 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 48 9 h10 kg_1828_48
    have h12 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 61 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 57 4 h11 kg_1828_57
    have h13 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 69 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 61 8 h12 kg_1828_61
    have h14 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 80 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 69 11 h13 kg_1828_69
    have h15 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 82 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 80 2 h14 kg_1828_80
    have h16 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 92 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 82 10 h15 kg_1828_82
    have h17 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 112 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 92 20 h16 kg_1828_92
    have h18 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 123 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 112 11 h17 kg_1828_112
    have h19 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 179 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 123 56 h18 kg_1828_123
    have h20 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 186 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 179 7 h19 kg_1828_179
    have h21 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 188 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 186 2 h20 kg_1828_186
    have h22 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 189 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 188 1 h21 kg_1828_188
    have h23 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 206 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 189 17 h22 kg_1828_189
    have h24 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 212 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 206 6 h23 kg_1828_206
    have h25 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 226 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 212 14 h24 kg_1828_212
    have h26 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 257 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 226 31 h25 kg_1828_226
    have h27 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 293 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 257 36 h26 kg_1828_257
    have h28 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 325 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 293 32 h27 kg_1828_293
    have h29 : IPChk.allR (Pts.glueIB K1828.lits KW_1828) 0 368 = true := IPChk.allR_join (Pts.glueIB K1828.lits KW_1828) 0 325 43 h28 kg_1828_325
    exact h29
  have hlen : K1828.lits.length = 368 := by decide
  intro k h1 h2
  obtain rfl : k = 1828 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1828) K1828.lits KW_1828
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_350 : ∀ k, 1829 ≤ k → k < 1868 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1829 JW_1829 1829 39 jr_1829
theorem jr6_351 : ∀ k, 1868 ≤ k → k < 1869 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 596 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 1 = true := kb_1868_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 1 2 h0 kb_1868_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 3 17 h1 kb_1868_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 20 2 h2 kb_1868_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 22 4 h3 kb_1868_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 26 2 h4 kb_1868_26
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 28 12 h5 kb_1868_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 40 1 h6 kb_1868_40
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 41 3 h7 kb_1868_41
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 44 10 h8 kb_1868_44
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 54 3 h9 kb_1868_54
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 57 7 h10 kb_1868_57
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 64 3 h11 kb_1868_64
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 67 9 h12 kb_1868_67
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 76 8 h13 kb_1868_76
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 84 11 h14 kb_1868_84
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 95 2 h15 kb_1868_95
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 97 10 h16 kb_1868_97
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 107 3 h17 kb_1868_107
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 110 4 h18 kb_1868_110
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 114 2 h19 kb_1868_114
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 116 12 h20 kb_1868_116
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 128 1 h21 kb_1868_128
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 129 4 h22 kb_1868_129
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 133 8 h23 kb_1868_133
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 141 7 h24 kb_1868_141
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 148 4 h25 kb_1868_148
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 152 11 h26 kb_1868_152
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 163 6 h27 kb_1868_163
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 169 8 h28 kb_1868_169
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 177 2 h29 kb_1868_177
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 179 1 h30 kb_1868_179
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 180 2 h31 kb_1868_180
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 182 13 h32 kb_1868_182
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 195 6 h33 kb_1868_195
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 201 4 h34 kb_1868_201
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 205 2 h35 kb_1868_205
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 219 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 207 12 h36 kb_1868_207
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 219 3 h37 kb_1868_219
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 222 4 h38 kb_1868_222
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 226 2 h39 kb_1868_226
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 228 12 h40 kb_1868_228
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 242 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 240 2 h41 kb_1868_240
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 257 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 242 15 h42 kb_1868_242
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 257 2 h43 kb_1868_257
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 259 2 h44 kb_1868_259
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 261 3 h45 kb_1868_261
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 264 7 h46 kb_1868_264
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 283 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 271 12 h47 kb_1868_271
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 283 18 h48 kb_1868_283
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 301 2 h49 kb_1868_301
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 303 3 h50 kb_1868_303
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 306 5 h51 kb_1868_306
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 311 28 h52 kb_1868_311
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 339 6 h53 kb_1868_339
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 345 36 h54 kb_1868_345
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 381 3 h55 kb_1868_381
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 384 3 h56 kb_1868_384
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 393 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 387 6 h57 kb_1868_387
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 393 10 h58 kb_1868_393
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 403 12 h59 kb_1868_403
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 426 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 415 11 h60 kb_1868_415
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 426 3 h61 kb_1868_426
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 429 3 h62 kb_1868_429
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 434 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 432 2 h63 kb_1868_432
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 434 2 h64 kb_1868_434
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 436 19 h65 kb_1868_436
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 455 11 h66 kb_1868_455
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 466 31 h67 kb_1868_466
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 497 36 h68 kb_1868_497
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 533 32 h69 kb_1868_533
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1868.lits.getD i 0)) 0 565 31 h70 kb_1868_565
    exact h71
  have hg : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 596 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 1 = true := kg_1868_0
    have h1 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 3 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 1 2 h0 kg_1868_1
    have h2 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 20 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 3 17 h1 kg_1868_3
    have h3 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 22 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 20 2 h2 kg_1868_20
    have h4 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 26 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 22 4 h3 kg_1868_22
    have h5 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 28 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 26 2 h4 kg_1868_26
    have h6 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 40 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 28 12 h5 kg_1868_28
    have h7 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 41 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 40 1 h6 kg_1868_40
    have h8 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 44 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 41 3 h7 kg_1868_41
    have h9 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 54 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 44 10 h8 kg_1868_44
    have h10 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 57 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 54 3 h9 kg_1868_54
    have h11 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 64 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 57 7 h10 kg_1868_57
    have h12 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 67 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 64 3 h11 kg_1868_64
    have h13 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 76 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 67 9 h12 kg_1868_67
    have h14 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 84 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 76 8 h13 kg_1868_76
    have h15 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 95 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 84 11 h14 kg_1868_84
    have h16 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 97 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 95 2 h15 kg_1868_95
    have h17 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 107 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 97 10 h16 kg_1868_97
    have h18 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 110 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 107 3 h17 kg_1868_107
    have h19 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 114 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 110 4 h18 kg_1868_110
    have h20 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 116 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 114 2 h19 kg_1868_114
    have h21 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 128 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 116 12 h20 kg_1868_116
    have h22 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 129 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 128 1 h21 kg_1868_128
    have h23 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 133 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 129 4 h22 kg_1868_129
    have h24 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 141 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 133 8 h23 kg_1868_133
    have h25 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 148 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 141 7 h24 kg_1868_141
    have h26 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 152 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 148 4 h25 kg_1868_148
    have h27 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 163 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 152 11 h26 kg_1868_152
    have h28 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 169 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 163 6 h27 kg_1868_163
    have h29 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 177 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 169 8 h28 kg_1868_169
    have h30 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 179 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 177 2 h29 kg_1868_177
    have h31 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 180 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 179 1 h30 kg_1868_179
    have h32 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 182 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 180 2 h31 kg_1868_180
    have h33 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 195 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 182 13 h32 kg_1868_182
    have h34 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 201 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 195 6 h33 kg_1868_195
    have h35 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 205 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 201 4 h34 kg_1868_201
    have h36 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 207 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 205 2 h35 kg_1868_205
    have h37 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 219 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 207 12 h36 kg_1868_207
    have h38 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 222 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 219 3 h37 kg_1868_219
    have h39 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 226 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 222 4 h38 kg_1868_222
    have h40 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 228 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 226 2 h39 kg_1868_226
    have h41 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 240 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 228 12 h40 kg_1868_228
    have h42 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 242 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 240 2 h41 kg_1868_240
    have h43 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 257 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 242 15 h42 kg_1868_242
    have h44 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 259 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 257 2 h43 kg_1868_257
    have h45 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 261 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 259 2 h44 kg_1868_259
    have h46 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 264 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 261 3 h45 kg_1868_261
    have h47 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 271 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 264 7 h46 kg_1868_264
    have h48 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 283 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 271 12 h47 kg_1868_271
    have h49 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 301 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 283 18 h48 kg_1868_283
    have h50 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 303 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 301 2 h49 kg_1868_301
    have h51 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 306 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 303 3 h50 kg_1868_303
    have h52 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 311 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 306 5 h51 kg_1868_306
    have h53 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 339 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 311 28 h52 kg_1868_311
    have h54 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 345 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 339 6 h53 kg_1868_339
    have h55 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 381 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 345 36 h54 kg_1868_345
    have h56 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 384 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 381 3 h55 kg_1868_381
    have h57 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 387 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 384 3 h56 kg_1868_384
    have h58 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 393 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 387 6 h57 kg_1868_387
    have h59 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 403 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 393 10 h58 kg_1868_393
    have h60 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 415 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 403 12 h59 kg_1868_403
    have h61 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 426 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 415 11 h60 kg_1868_415
    have h62 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 429 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 426 3 h61 kg_1868_426
    have h63 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 432 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 429 3 h62 kg_1868_429
    have h64 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 434 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 432 2 h63 kg_1868_432
    have h65 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 436 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 434 2 h64 kg_1868_434
    have h66 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 455 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 436 19 h65 kg_1868_436
    have h67 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 466 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 455 11 h66 kg_1868_455
    have h68 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 497 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 466 31 h67 kg_1868_466
    have h69 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 533 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 497 36 h68 kg_1868_497
    have h70 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 565 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 533 32 h69 kg_1868_533
    have h71 : IPChk.allR (Pts.glueIB K1868.lits KW_1868) 0 596 = true := IPChk.allR_join (Pts.glueIB K1868.lits KW_1868) 0 565 31 h70 kg_1868_565
    exact h71
  have hlen : K1868.lits.length = 596 := by decide
  intro k h1 h2
  obtain rfl : k = 1868 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1868) K1868.lits KW_1868
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_352 : ∀ k, 1869 ≤ k → k < 1897 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1869 JW_1869 1869 28 jr_1869
theorem jr6_353 : ∀ k, 1897 ≤ k → k < 1898 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 279 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 1 = true := kb_1897_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 1 2 h0 kb_1897_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 3 35 h1 kb_1897_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 38 24 h2 kb_1897_38
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 62 15 h3 kb_1897_62
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 77 57 h4 kb_1897_77
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 134 20 h5 kb_1897_134
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 154 23 h6 kb_1897_154
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 177 6 h7 kb_1897_177
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 183 3 h8 kb_1897_183
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 186 20 h9 kb_1897_186
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 206 20 h10 kb_1897_206
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 226 17 h11 kb_1897_226
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 243 5 h12 kb_1897_243
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 0 248 31 h13 kb_1897_248
    exact h14
  have hg : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 279 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 1 = true := kg_1897_0
    have h1 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 3 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 1 2 h0 kg_1897_1
    have h2 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 38 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 3 35 h1 kg_1897_3
    have h3 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 62 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 38 24 h2 kg_1897_38
    have h4 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 77 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 62 15 h3 kg_1897_62
    have h5 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 134 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 77 57 h4 kg_1897_77
    have h6 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 154 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 134 20 h5 kg_1897_134
    have h7 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 177 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 154 23 h6 kg_1897_154
    have h8 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 183 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 177 6 h7 kg_1897_177
    have h9 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 186 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 183 3 h8 kg_1897_183
    have h10 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 206 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 186 20 h9 kg_1897_186
    have h11 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 226 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 206 20 h10 kg_1897_206
    have h12 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 243 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 226 17 h11 kg_1897_226
    have h13 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 248 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 243 5 h12 kg_1897_243
    have h14 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 0 279 = true := IPChk.allR_join (Pts.glueIB K1897.lits KW_1897) 0 248 31 h13 kg_1897_248
    exact h14
  have hlen : K1897.lits.length = 279 := by decide
  intro k h1 h2
  obtain rfl : k = 1897 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1897) K1897.lits KW_1897
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_354 : ∀ k, 1898 ≤ k → k < 1930 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1898 JW_1898 1898 32 jr_1898
theorem jr6_355 : ∀ k, 1930 ≤ k → k < 1931 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 348 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 1 = true := kb_1930_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 1 13 h0 kb_1930_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 14 6 h1 kb_1930_14
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 20 12 h2 kb_1930_20
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 32 1 h3 kb_1930_32
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 33 2 h4 kb_1930_33
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 35 9 h5 kb_1930_35
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 44 22 h6 kb_1930_44
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 66 2 h7 kb_1930_66
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 68 6 h8 kb_1930_68
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 74 2 h9 kb_1930_74
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 76 14 h10 kb_1930_76
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 90 7 h11 kb_1930_90
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 97 2 h12 kb_1930_97
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 99 8 h13 kb_1930_99
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 107 2 h14 kb_1930_107
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 109 13 h15 kb_1930_109
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 122 10 h16 kb_1930_122
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 132 2 h17 kb_1930_132
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 134 22 h18 kb_1930_134
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 156 1 h19 kb_1930_156
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 157 1 h20 kb_1930_157
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 158 1 h21 kb_1930_158
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 159 1 h22 kb_1930_159
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 160 6 h23 kb_1930_160
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 166 13 h24 kb_1930_166
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 179 11 h25 kb_1930_179
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 190 12 h26 kb_1930_190
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 202 15 h27 kb_1930_202
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 217 16 h28 kb_1930_217
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 233 14 h29 kb_1930_233
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 247 3 h30 kb_1930_247
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 250 9 h31 kb_1930_250
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 293 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 259 34 h32 kb_1930_259
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 295 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 293 2 h33 kb_1930_293
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 304 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 295 9 h34 kb_1930_295
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 304 3 h35 kb_1930_304
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 307 38 h36 kb_1930_307
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1930.lits.getD i 0)) 0 345 3 h37 kb_1930_345
    exact h38
  have hg : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 348 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 1 = true := kg_1930_0
    have h1 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 14 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 1 13 h0 kg_1930_1
    have h2 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 20 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 14 6 h1 kg_1930_14
    have h3 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 32 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 20 12 h2 kg_1930_20
    have h4 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 33 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 32 1 h3 kg_1930_32
    have h5 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 35 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 33 2 h4 kg_1930_33
    have h6 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 44 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 35 9 h5 kg_1930_35
    have h7 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 66 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 44 22 h6 kg_1930_44
    have h8 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 68 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 66 2 h7 kg_1930_66
    have h9 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 74 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 68 6 h8 kg_1930_68
    have h10 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 76 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 74 2 h9 kg_1930_74
    have h11 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 90 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 76 14 h10 kg_1930_76
    have h12 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 97 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 90 7 h11 kg_1930_90
    have h13 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 99 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 97 2 h12 kg_1930_97
    have h14 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 107 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 99 8 h13 kg_1930_99
    have h15 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 109 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 107 2 h14 kg_1930_107
    have h16 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 122 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 109 13 h15 kg_1930_109
    have h17 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 132 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 122 10 h16 kg_1930_122
    have h18 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 134 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 132 2 h17 kg_1930_132
    have h19 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 156 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 134 22 h18 kg_1930_134
    have h20 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 157 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 156 1 h19 kg_1930_156
    have h21 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 158 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 157 1 h20 kg_1930_157
    have h22 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 159 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 158 1 h21 kg_1930_158
    have h23 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 160 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 159 1 h22 kg_1930_159
    have h24 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 166 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 160 6 h23 kg_1930_160
    have h25 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 179 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 166 13 h24 kg_1930_166
    have h26 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 190 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 179 11 h25 kg_1930_179
    have h27 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 202 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 190 12 h26 kg_1930_190
    have h28 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 217 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 202 15 h27 kg_1930_202
    have h29 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 233 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 217 16 h28 kg_1930_217
    have h30 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 247 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 233 14 h29 kg_1930_233
    have h31 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 250 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 247 3 h30 kg_1930_247
    have h32 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 259 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 250 9 h31 kg_1930_250
    have h33 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 293 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 259 34 h32 kg_1930_259
    have h34 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 295 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 293 2 h33 kg_1930_293
    have h35 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 304 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 295 9 h34 kg_1930_295
    have h36 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 307 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 304 3 h35 kg_1930_304
    have h37 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 345 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 307 38 h36 kg_1930_307
    have h38 : IPChk.allR (Pts.glueIB K1930.lits KW_1930) 0 348 = true := IPChk.allR_join (Pts.glueIB K1930.lits KW_1930) 0 345 3 h37 kg_1930_345
    exact h38
  have hlen : K1930.lits.length = 348 := by decide
  intro k h1 h2
  obtain rfl : k = 1930 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1930) K1930.lits KW_1930
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_356 : ∀ k, 1931 ≤ k → k < 1932 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 113 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 15 = true := kb_1931_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 15 2 h0 kb_1931_15
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 17 14 h1 kb_1931_17
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 31 6 h2 kb_1931_31
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 37 5 h3 kb_1931_37
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 42 14 h4 kb_1931_42
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 56 28 h5 kb_1931_56
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 84 2 h6 kb_1931_84
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 86 1 h7 kb_1931_86
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 87 14 h8 kb_1931_87
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1931.lits.getD i 0)) 0 101 12 h9 kb_1931_101
    exact h10
  have hg : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 113 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 15 = true := kg_1931_0
    have h1 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 17 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 15 2 h0 kg_1931_15
    have h2 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 31 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 17 14 h1 kg_1931_17
    have h3 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 37 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 31 6 h2 kg_1931_31
    have h4 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 42 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 37 5 h3 kg_1931_37
    have h5 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 56 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 42 14 h4 kg_1931_42
    have h6 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 84 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 56 28 h5 kg_1931_56
    have h7 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 86 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 84 2 h6 kg_1931_84
    have h8 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 87 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 86 1 h7 kg_1931_86
    have h9 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 101 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 87 14 h8 kg_1931_87
    have h10 : IPChk.allR (Pts.glueIB K1931.lits KW_1931) 0 113 = true := IPChk.allR_join (Pts.glueIB K1931.lits KW_1931) 0 101 12 h9 kg_1931_101
    exact h10
  have hlen : K1931.lits.length = 113 := by decide
  intro k h1 h2
  obtain rfl : k = 1931 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1931) K1931.lits KW_1931
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)

theorem grp6_13 : ∀ k, 1732 ≤ k → k < 1932 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_337
  have a1 := Pts.fa_join a0 jr6_338
  have a2 := Pts.fa_join a1 jr6_339
  have a3 := Pts.fa_join a2 jr6_340
  have a4 := Pts.fa_join a3 jr6_341
  have a5 := Pts.fa_join a4 jr6_342
  have a6 := Pts.fa_join a5 jr6_343
  have a7 := Pts.fa_join a6 jr6_344
  have a8 := Pts.fa_join a7 jr6_345
  have a9 := Pts.fa_join a8 jr6_346
  have a10 := Pts.fa_join a9 jr6_347
  have a11 := Pts.fa_join a10 jr6_348
  have a12 := Pts.fa_join a11 jr6_349
  have a13 := Pts.fa_join a12 jr6_350
  have a14 := Pts.fa_join a13 jr6_351
  have a15 := Pts.fa_join a14 jr6_352
  have a16 := Pts.fa_join a15 jr6_353
  have a17 := Pts.fa_join a16 jr6_354
  have a18 := Pts.fa_join a17 jr6_355
  have a19 := Pts.fa_join a18 jr6_356
  exact a19

end B334.E1x.Pts.S707
