import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J1348
import B334.E1x.Pts.S707.J1350
import B334.E1x.Pts.S707.J1354
import B334.E1x.Pts.S707.J1356
import B334.E1x.Pts.S707.K1347L
import B334.E1x.Pts.S707.K1349L
import B334.E1x.Pts.S707.K1352L
import B334.E1x.Pts.S707.K1353L
import B334.E1x.Pts.S707.K1355L
import B334.E1x.Pts.S707.K1347Q0
import B334.E1x.Pts.S707.K1347Q1
import B334.E1x.Pts.S707.K1347Q2
import B334.E1x.Pts.S707.K1347Q3
import B334.E1x.Pts.S707.K1347Q4
import B334.E1x.Pts.S707.K1347Q5
import B334.E1x.Pts.S707.K1347Q6
import B334.E1x.Pts.S707.K1347Q7
import B334.E1x.Pts.S707.K1347Q8
import B334.E1x.Pts.S707.K1347Q9
import B334.E1x.Pts.S707.K1349Q0
import B334.E1x.Pts.S707.K1349Q1
import B334.E1x.Pts.S707.K1349Q2
import B334.E1x.Pts.S707.K1349Q3
import B334.E1x.Pts.S707.K1349Q4
import B334.E1x.Pts.S707.K1349Q5
import B334.E1x.Pts.S707.K1349Q6
import B334.E1x.Pts.S707.K1349Q7
import B334.E1x.Pts.S707.K1349Q8
import B334.E1x.Pts.S707.K1349Q9
import B334.E1x.Pts.S707.K1352Q0
import B334.E1x.Pts.S707.K1352Q1
import B334.E1x.Pts.S707.K1352Q2
import B334.E1x.Pts.S707.K1352Q3
import B334.E1x.Pts.S707.K1353Q0
import B334.E1x.Pts.S707.K1353Q1
import B334.E1x.Pts.S707.K1353Q2
import B334.E1x.Pts.S707.K1353Q3
import B334.E1x.Pts.S707.K1355Q0
import B334.E1x.Pts.S707.K1355Q1
import B334.E1x.Pts.S707.K1355Q2
import B334.E1x.Pts.S707.K1355Q3
import B334.E1x.Pts.S707.K1355Q4
import B334.E1x.Pts.S707.K1355Q5
import B334.E1x.Pts.S707.K1355Q6
import B334.E1x.Pts.S707.K1355Q7
import B334.E1x.Pts.S707.K1355Q8
import B334.E1x.Pts.S707.K1355Q9
import B334.E1x.Pts.S707.K1347Q10
import B334.E1x.Pts.S707.K1347Q11
import B334.E1x.Pts.S707.K1347Q12
import B334.E1x.Pts.S707.K1347Q13
import B334.E1x.Pts.S707.K1347Q14
import B334.E1x.Pts.S707.K1347Q15
import B334.E1x.Pts.S707.K1347Q16
import B334.E1x.Pts.S707.K1347Q17
import B334.E1x.Pts.S707.K1347Q18
import B334.E1x.Pts.S707.K1349Q10
import B334.E1x.Pts.S707.K1349Q11
import B334.E1x.Pts.S707.K1349Q12
import B334.E1x.Pts.S707.K1349Q13
import B334.E1x.Pts.S707.K1349Q14
import B334.E1x.Pts.S707.K1349Q15
import B334.E1x.Pts.S707.K1349Q16
import B334.E1x.Pts.S707.K1349Q17
import B334.E1x.Pts.S707.K1349Q18
import B334.E1x.Pts.S707.K1349Q19
import B334.E1x.Pts.S707.K1349Q20
import B334.E1x.Pts.S707.K1349Q21
import B334.E1x.Pts.S707.K1349Q22
import B334.E1x.Pts.S707.K1349Q23
import B334.E1x.Pts.S707.K1349Q24
import B334.E1x.Pts.S707.K1349Q25

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 1347 … 1405 (stage707_v6): the v5 Fin's job blocks r278 … r286 as
theorems, joined into `grp6_10` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_278 : ∀ k, 1347 ≤ k → k < 1348 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2060 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1 = true := kb_1347_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1 4 h0 kb_1347_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 5 2 h1 kb_1347_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 7 8 h2 kb_1347_7
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 15 8 h3 kb_1347_15
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 23 3 h4 kb_1347_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 26 3 h5 kb_1347_26
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 29 1 h6 kb_1347_29
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 30 13 h7 kb_1347_30
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 43 14 h8 kb_1347_43
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 57 3 h9 kb_1347_57
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 60 14 h10 kb_1347_60
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 74 1 h11 kb_1347_74
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 75 16 h12 kb_1347_75
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 91 15 h13 kb_1347_91
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 106 6 h14 kb_1347_106
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 112 2 h15 kb_1347_112
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 114 20 h16 kb_1347_114
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 134 1 h17 kb_1347_134
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 135 1 h18 kb_1347_135
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 136 3 h19 kb_1347_136
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 139 23 h20 kb_1347_139
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 162 1 h21 kb_1347_162
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 163 1 h22 kb_1347_163
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 164 1 h23 kb_1347_164
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 165 6 h24 kb_1347_165
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 171 1 h25 kb_1347_171
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 172 1 h26 kb_1347_172
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 173 2 h27 kb_1347_173
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 175 29 h28 kb_1347_175
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 204 2 h29 kb_1347_204
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 206 6 h30 kb_1347_206
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 212 2 h31 kb_1347_212
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 214 22 h32 kb_1347_214
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 236 3 h33 kb_1347_236
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 239 6 h34 kb_1347_239
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 245 52 h35 kb_1347_245
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 297 12 h36 kb_1347_297
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 309 1 h37 kb_1347_309
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 310 1 h38 kb_1347_310
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 311 21 h39 kb_1347_311
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 332 10 h40 kb_1347_332
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 342 6 h41 kb_1347_342
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 348 2 h42 kb_1347_348
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 350 20 h43 kb_1347_350
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 370 2 h44 kb_1347_370
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 372 3 h45 kb_1347_372
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 375 3 h46 kb_1347_375
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 378 2 h47 kb_1347_378
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 380 29 h48 kb_1347_380
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 409 2 h49 kb_1347_409
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 411 6 h50 kb_1347_411
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 417 2 h51 kb_1347_417
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 441 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 419 22 h52 kb_1347_419
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 441 3 h53 kb_1347_441
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 444 6 h54 kb_1347_444
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 450 23 h55 kb_1347_450
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 473 18 h56 kb_1347_473
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 491 11 h57 kb_1347_491
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 502 5 h58 kb_1347_502
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 507 25 h59 kb_1347_507
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 532 2 h60 kb_1347_532
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 534 14 h61 kb_1347_534
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 548 15 h62 kb_1347_548
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 563 21 h63 kb_1347_563
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 584 19 h64 kb_1347_584
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 603 17 h65 kb_1347_603
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 647 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 620 27 h66 kb_1347_620
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 649 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 647 2 h67 kb_1347_647
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 660 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 649 11 h68 kb_1347_649
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 660 1 h69 kb_1347_660
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 661 1 h70 kb_1347_661
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 662 29 h71 kb_1347_662
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 691 2 h72 kb_1347_691
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 693 6 h73 kb_1347_693
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 699 2 h74 kb_1347_699
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 701 22 h75 kb_1347_701
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 723 3 h76 kb_1347_723
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 726 7 h77 kb_1347_726
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 794 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 733 61 h78 kb_1347_733
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 794 8 h79 kb_1347_794
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 802 2 h80 kb_1347_802
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 805 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 804 1 h81 kb_1347_804
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 806 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 805 1 h82 kb_1347_805
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 807 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 806 1 h83 kb_1347_806
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 812 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 807 5 h84 kb_1347_807
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 816 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 812 4 h85 kb_1347_812
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 821 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 816 5 h86 kb_1347_816
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 821 8 h87 kb_1347_821
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 829 5 h88 kb_1347_829
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 836 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 834 2 h89 kb_1347_834
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 836 8 h90 kb_1347_836
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 847 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 844 3 h91 kb_1347_844
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 853 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 847 6 h92 kb_1347_847
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 861 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 853 8 h93 kb_1347_853
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 866 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 861 5 h94 kb_1347_861
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 873 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 866 7 h95 kb_1347_866
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 873 2 h96 kb_1347_873
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 876 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 875 1 h97 kb_1347_875
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 876 1 h98 kb_1347_876
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 904 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 877 27 h99 kb_1347_877
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 908 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 904 4 h100 kb_1347_904
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 908 12 h101 kb_1347_908
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 943 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 920 23 h102 kb_1347_920
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 945 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 943 2 h103 kb_1347_943
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 970 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 945 25 h104 kb_1347_945
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 973 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 970 3 h105 kb_1347_970
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 986 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 973 13 h106 kb_1347_973
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 990 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 986 4 h107 kb_1347_986
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1012 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 990 22 h108 kb_1347_990
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1012 16 h109 kb_1347_1012
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1055 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1028 27 h110 kb_1347_1028
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1056 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1055 1 h111 kb_1347_1055
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1066 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1056 10 h112 kb_1347_1056
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1073 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1066 7 h113 kb_1347_1066
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1084 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1073 11 h114 kb_1347_1073
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1086 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1084 2 h115 kb_1347_1084
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1086 11 h116 kb_1347_1086
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1097 24 h117 kb_1347_1097
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1121 3 h118 kb_1347_1121
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1124 4 h119 kb_1347_1124
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1128 9 h120 kb_1347_1128
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1137 9 h121 kb_1347_1137
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1146 13 h122 kb_1347_1146
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1159 14 h123 kb_1347_1159
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1173 25 h124 kb_1347_1173
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1198 15 h125 kb_1347_1198
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1213 31 h126 kb_1347_1213
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1244 36 h127 kb_1347_1244
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1280 18 h128 kb_1347_1280
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1298 1 h129 kb_1347_1298
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1299 1 h130 kb_1347_1299
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1300 2 h131 kb_1347_1300
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1302 1 h132 kb_1347_1302
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1303 4 h133 kb_1347_1303
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1307 2 h134 kb_1347_1307
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1309 1 h135 kb_1347_1309
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1314 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1310 4 h136 kb_1347_1310
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1314 5 h137 kb_1347_1314
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1319 4 h138 kb_1347_1319
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1323 5 h139 kb_1347_1323
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1328 1 h140 kb_1347_1328
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1329 4 h141 kb_1347_1329
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1333 12 h142 kb_1347_1333
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1345 21 h143 kb_1347_1345
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1366 6 h144 kb_1347_1366
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1372 6 h145 kb_1347_1372
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1378 71 h146 kb_1347_1378
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1449 17 h147 kb_1347_1449
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1466 14 h148 kb_1347_1466
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1480 1 h149 kb_1347_1480
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1483 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1481 2 h150 kb_1347_1481
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1483 2 h151 kb_1347_1483
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1485 7 h152 kb_1347_1485
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1492 25 h153 kb_1347_1492
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1523 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1517 6 h154 kb_1347_1517
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1523 6 h155 kb_1347_1523
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1535 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1529 6 h156 kb_1347_1529
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1535 72 h157 kb_1347_1535
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1638 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1607 31 h158 kb_1347_1607
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1638 53 h159 kb_1347_1638
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1691 31 h160 kb_1347_1691
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1728 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1722 6 h161 kb_1347_1722
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1728 4 h162 kb_1347_1728
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1759 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1732 27 h163 kb_1347_1732
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1832 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1759 73 h164 kb_1347_1759
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1832 9 h165 kb_1347_1832
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1857 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1841 16 h166 kb_1347_1841
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1857 20 h167 kb_1347_1857
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1877 26 h168 kb_1347_1877
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1908 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1903 5 h169 kb_1347_1903
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1908 6 h170 kb_1347_1908
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1926 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1914 12 h171 kb_1347_1914
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1979 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1926 53 h172 kb_1347_1926
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2000 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 1979 21 h173 kb_1347_1979
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2005 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2000 5 h174 kb_1347_2000
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2009 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2005 4 h175 kb_1347_2005
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2009 4 h176 kb_1347_2009
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2014 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2013 1 h177 kb_1347_2013
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2015 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2014 1 h178 kb_1347_2014
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2017 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2015 2 h179 kb_1347_2015
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2019 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2017 2 h180 kb_1347_2017
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2032 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2019 13 h181 kb_1347_2019
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2048 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2032 16 h182 kb_1347_2032
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2055 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2048 7 h183 kb_1347_2048
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2060 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 0 2055 5 h184 kb_1347_2055
    exact h185
  have hg : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2060 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1 = true := kg_1347_0
    have h1 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 5 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1 4 h0 kg_1347_1
    have h2 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 7 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 5 2 h1 kg_1347_5
    have h3 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 15 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 7 8 h2 kg_1347_7
    have h4 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 23 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 15 8 h3 kg_1347_15
    have h5 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 26 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 23 3 h4 kg_1347_23
    have h6 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 29 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 26 3 h5 kg_1347_26
    have h7 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 30 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 29 1 h6 kg_1347_29
    have h8 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 43 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 30 13 h7 kg_1347_30
    have h9 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 57 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 43 14 h8 kg_1347_43
    have h10 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 60 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 57 3 h9 kg_1347_57
    have h11 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 74 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 60 14 h10 kg_1347_60
    have h12 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 75 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 74 1 h11 kg_1347_74
    have h13 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 91 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 75 16 h12 kg_1347_75
    have h14 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 106 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 91 15 h13 kg_1347_91
    have h15 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 112 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 106 6 h14 kg_1347_106
    have h16 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 114 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 112 2 h15 kg_1347_112
    have h17 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 134 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 114 20 h16 kg_1347_114
    have h18 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 135 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 134 1 h17 kg_1347_134
    have h19 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 136 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 135 1 h18 kg_1347_135
    have h20 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 139 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 136 3 h19 kg_1347_136
    have h21 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 162 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 139 23 h20 kg_1347_139
    have h22 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 163 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 162 1 h21 kg_1347_162
    have h23 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 164 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 163 1 h22 kg_1347_163
    have h24 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 165 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 164 1 h23 kg_1347_164
    have h25 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 171 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 165 6 h24 kg_1347_165
    have h26 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 172 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 171 1 h25 kg_1347_171
    have h27 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 173 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 172 1 h26 kg_1347_172
    have h28 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 175 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 173 2 h27 kg_1347_173
    have h29 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 204 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 175 29 h28 kg_1347_175
    have h30 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 206 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 204 2 h29 kg_1347_204
    have h31 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 212 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 206 6 h30 kg_1347_206
    have h32 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 214 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 212 2 h31 kg_1347_212
    have h33 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 236 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 214 22 h32 kg_1347_214
    have h34 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 239 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 236 3 h33 kg_1347_236
    have h35 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 245 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 239 6 h34 kg_1347_239
    have h36 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 297 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 245 52 h35 kg_1347_245
    have h37 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 309 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 297 12 h36 kg_1347_297
    have h38 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 310 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 309 1 h37 kg_1347_309
    have h39 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 311 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 310 1 h38 kg_1347_310
    have h40 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 332 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 311 21 h39 kg_1347_311
    have h41 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 342 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 332 10 h40 kg_1347_332
    have h42 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 348 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 342 6 h41 kg_1347_342
    have h43 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 350 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 348 2 h42 kg_1347_348
    have h44 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 370 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 350 20 h43 kg_1347_350
    have h45 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 372 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 370 2 h44 kg_1347_370
    have h46 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 375 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 372 3 h45 kg_1347_372
    have h47 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 378 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 375 3 h46 kg_1347_375
    have h48 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 380 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 378 2 h47 kg_1347_378
    have h49 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 409 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 380 29 h48 kg_1347_380
    have h50 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 411 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 409 2 h49 kg_1347_409
    have h51 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 417 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 411 6 h50 kg_1347_411
    have h52 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 419 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 417 2 h51 kg_1347_417
    have h53 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 441 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 419 22 h52 kg_1347_419
    have h54 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 444 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 441 3 h53 kg_1347_441
    have h55 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 450 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 444 6 h54 kg_1347_444
    have h56 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 473 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 450 23 h55 kg_1347_450
    have h57 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 491 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 473 18 h56 kg_1347_473
    have h58 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 502 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 491 11 h57 kg_1347_491
    have h59 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 507 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 502 5 h58 kg_1347_502
    have h60 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 532 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 507 25 h59 kg_1347_507
    have h61 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 534 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 532 2 h60 kg_1347_532
    have h62 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 548 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 534 14 h61 kg_1347_534
    have h63 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 563 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 548 15 h62 kg_1347_548
    have h64 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 584 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 563 21 h63 kg_1347_563
    have h65 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 603 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 584 19 h64 kg_1347_584
    have h66 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 620 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 603 17 h65 kg_1347_603
    have h67 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 647 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 620 27 h66 kg_1347_620
    have h68 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 649 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 647 2 h67 kg_1347_647
    have h69 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 660 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 649 11 h68 kg_1347_649
    have h70 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 661 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 660 1 h69 kg_1347_660
    have h71 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 662 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 661 1 h70 kg_1347_661
    have h72 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 691 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 662 29 h71 kg_1347_662
    have h73 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 693 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 691 2 h72 kg_1347_691
    have h74 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 699 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 693 6 h73 kg_1347_693
    have h75 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 701 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 699 2 h74 kg_1347_699
    have h76 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 723 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 701 22 h75 kg_1347_701
    have h77 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 726 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 723 3 h76 kg_1347_723
    have h78 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 733 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 726 7 h77 kg_1347_726
    have h79 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 794 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 733 61 h78 kg_1347_733
    have h80 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 802 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 794 8 h79 kg_1347_794
    have h81 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 804 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 802 2 h80 kg_1347_802
    have h82 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 805 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 804 1 h81 kg_1347_804
    have h83 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 806 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 805 1 h82 kg_1347_805
    have h84 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 807 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 806 1 h83 kg_1347_806
    have h85 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 812 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 807 5 h84 kg_1347_807
    have h86 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 816 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 812 4 h85 kg_1347_812
    have h87 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 821 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 816 5 h86 kg_1347_816
    have h88 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 829 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 821 8 h87 kg_1347_821
    have h89 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 834 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 829 5 h88 kg_1347_829
    have h90 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 836 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 834 2 h89 kg_1347_834
    have h91 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 844 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 836 8 h90 kg_1347_836
    have h92 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 847 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 844 3 h91 kg_1347_844
    have h93 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 853 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 847 6 h92 kg_1347_847
    have h94 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 861 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 853 8 h93 kg_1347_853
    have h95 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 866 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 861 5 h94 kg_1347_861
    have h96 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 873 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 866 7 h95 kg_1347_866
    have h97 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 875 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 873 2 h96 kg_1347_873
    have h98 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 876 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 875 1 h97 kg_1347_875
    have h99 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 877 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 876 1 h98 kg_1347_876
    have h100 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 904 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 877 27 h99 kg_1347_877
    have h101 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 908 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 904 4 h100 kg_1347_904
    have h102 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 920 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 908 12 h101 kg_1347_908
    have h103 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 943 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 920 23 h102 kg_1347_920
    have h104 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 945 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 943 2 h103 kg_1347_943
    have h105 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 970 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 945 25 h104 kg_1347_945
    have h106 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 973 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 970 3 h105 kg_1347_970
    have h107 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 986 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 973 13 h106 kg_1347_973
    have h108 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 990 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 986 4 h107 kg_1347_986
    have h109 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1012 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 990 22 h108 kg_1347_990
    have h110 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1028 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1012 16 h109 kg_1347_1012
    have h111 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1055 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1028 27 h110 kg_1347_1028
    have h112 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1056 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1055 1 h111 kg_1347_1055
    have h113 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1066 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1056 10 h112 kg_1347_1056
    have h114 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1073 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1066 7 h113 kg_1347_1066
    have h115 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1084 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1073 11 h114 kg_1347_1073
    have h116 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1086 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1084 2 h115 kg_1347_1084
    have h117 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1097 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1086 11 h116 kg_1347_1086
    have h118 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1121 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1097 24 h117 kg_1347_1097
    have h119 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1124 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1121 3 h118 kg_1347_1121
    have h120 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1128 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1124 4 h119 kg_1347_1124
    have h121 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1137 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1128 9 h120 kg_1347_1128
    have h122 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1146 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1137 9 h121 kg_1347_1137
    have h123 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1159 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1146 13 h122 kg_1347_1146
    have h124 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1173 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1159 14 h123 kg_1347_1159
    have h125 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1198 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1173 25 h124 kg_1347_1173
    have h126 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1213 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1198 15 h125 kg_1347_1198
    have h127 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1244 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1213 31 h126 kg_1347_1213
    have h128 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1280 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1244 36 h127 kg_1347_1244
    have h129 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1298 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1280 18 h128 kg_1347_1280
    have h130 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1299 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1298 1 h129 kg_1347_1298
    have h131 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1300 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1299 1 h130 kg_1347_1299
    have h132 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1302 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1300 2 h131 kg_1347_1300
    have h133 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1303 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1302 1 h132 kg_1347_1302
    have h134 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1307 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1303 4 h133 kg_1347_1303
    have h135 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1309 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1307 2 h134 kg_1347_1307
    have h136 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1310 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1309 1 h135 kg_1347_1309
    have h137 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1314 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1310 4 h136 kg_1347_1310
    have h138 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1319 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1314 5 h137 kg_1347_1314
    have h139 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1323 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1319 4 h138 kg_1347_1319
    have h140 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1328 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1323 5 h139 kg_1347_1323
    have h141 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1329 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1328 1 h140 kg_1347_1328
    have h142 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1333 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1329 4 h141 kg_1347_1329
    have h143 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1345 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1333 12 h142 kg_1347_1333
    have h144 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1366 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1345 21 h143 kg_1347_1345
    have h145 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1372 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1366 6 h144 kg_1347_1366
    have h146 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1378 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1372 6 h145 kg_1347_1372
    have h147 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1449 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1378 71 h146 kg_1347_1378
    have h148 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1466 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1449 17 h147 kg_1347_1449
    have h149 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1480 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1466 14 h148 kg_1347_1466
    have h150 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1481 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1480 1 h149 kg_1347_1480
    have h151 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1483 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1481 2 h150 kg_1347_1481
    have h152 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1485 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1483 2 h151 kg_1347_1483
    have h153 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1492 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1485 7 h152 kg_1347_1485
    have h154 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1517 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1492 25 h153 kg_1347_1492
    have h155 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1523 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1517 6 h154 kg_1347_1517
    have h156 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1529 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1523 6 h155 kg_1347_1523
    have h157 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1535 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1529 6 h156 kg_1347_1529
    have h158 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1607 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1535 72 h157 kg_1347_1535
    have h159 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1638 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1607 31 h158 kg_1347_1607
    have h160 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1691 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1638 53 h159 kg_1347_1638
    have h161 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1722 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1691 31 h160 kg_1347_1691
    have h162 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1728 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1722 6 h161 kg_1347_1722
    have h163 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1732 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1728 4 h162 kg_1347_1728
    have h164 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1759 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1732 27 h163 kg_1347_1732
    have h165 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1832 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1759 73 h164 kg_1347_1759
    have h166 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1841 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1832 9 h165 kg_1347_1832
    have h167 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1857 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1841 16 h166 kg_1347_1841
    have h168 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1877 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1857 20 h167 kg_1347_1857
    have h169 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1903 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1877 26 h168 kg_1347_1877
    have h170 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1908 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1903 5 h169 kg_1347_1903
    have h171 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1914 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1908 6 h170 kg_1347_1908
    have h172 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1926 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1914 12 h171 kg_1347_1914
    have h173 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 1979 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1926 53 h172 kg_1347_1926
    have h174 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2000 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 1979 21 h173 kg_1347_1979
    have h175 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2005 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2000 5 h174 kg_1347_2000
    have h176 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2009 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2005 4 h175 kg_1347_2005
    have h177 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2013 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2009 4 h176 kg_1347_2009
    have h178 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2014 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2013 1 h177 kg_1347_2013
    have h179 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2015 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2014 1 h178 kg_1347_2014
    have h180 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2017 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2015 2 h179 kg_1347_2015
    have h181 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2019 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2017 2 h180 kg_1347_2017
    have h182 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2032 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2019 13 h181 kg_1347_2019
    have h183 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2048 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2032 16 h182 kg_1347_2032
    have h184 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2055 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2048 7 h183 kg_1347_2048
    have h185 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 0 2060 = true := IPChk.allR_join (Pts.glueIB K1347.lits KW_1347) 0 2055 5 h184 kg_1347_2055
    exact h185
  have hlen : K1347.lits.length = 2060 := by decide
  intro k h1 h2
  obtain rfl : k = 1347 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1347) K1347.lits KW_1347
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_279 : ∀ k, 1348 ≤ k → k < 1349 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1348 JW_1348 1348 1 jr_1348
theorem jr6_280 : ∀ k, 1349 ≤ k → k < 1350 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2117 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 6 = true := kb_1349_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 6 8 h0 kb_1349_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 14 8 h1 kb_1349_14
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 22 1 h2 kb_1349_22
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 23 5 h3 kb_1349_23
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 28 15 h4 kb_1349_28
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 43 2 h5 kb_1349_43
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 45 12 h6 kb_1349_45
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 57 1 h7 kb_1349_57
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 58 11 h8 kb_1349_58
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 69 18 h9 kb_1349_69
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 87 2 h10 kb_1349_87
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 89 6 h11 kb_1349_89
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 95 2 h12 kb_1349_95
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 97 17 h13 kb_1349_97
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 114 6 h14 kb_1349_114
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 120 1 h15 kb_1349_120
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 121 1 h16 kb_1349_121
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 122 2 h17 kb_1349_122
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 124 8 h18 kb_1349_124
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 132 22 h19 kb_1349_132
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 154 2 h20 kb_1349_154
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 156 3 h21 kb_1349_156
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 159 3 h22 kb_1349_159
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 162 1 h23 kb_1349_162
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 163 1 h24 kb_1349_163
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 164 1 h25 kb_1349_164
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 165 20 h26 kb_1349_165
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 185 11 h27 kb_1349_185
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 196 6 h28 kb_1349_196
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 202 2 h29 kb_1349_202
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 204 13 h30 kb_1349_204
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 217 10 h31 kb_1349_217
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 227 2 h32 kb_1349_227
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 229 3 h33 kb_1349_229
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 232 2 h34 kb_1349_232
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 234 1 h35 kb_1349_234
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 235 26 h36 kb_1349_235
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 266 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 261 5 h37 kb_1349_261
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 266 6 h38 kb_1349_266
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 272 2 h39 kb_1349_272
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 274 22 h40 kb_1349_274
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 296 3 h41 kb_1349_296
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 299 7 h42 kb_1349_299
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 306 36 h43 kb_1349_306
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 342 14 h44 kb_1349_342
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 356 4 h45 kb_1349_356
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 360 12 h46 kb_1349_360
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 372 15 h47 kb_1349_372
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 387 2 h48 kb_1349_387
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 389 12 h49 kb_1349_389
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 401 12 h50 kb_1349_401
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 413 8 h51 kb_1349_413
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 435 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 421 14 h52 kb_1349_421
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 435 7 h53 kb_1349_435
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 442 3 h54 kb_1349_442
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 467 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 445 22 h55 kb_1349_445
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 467 1 h56 kb_1349_467
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 469 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 468 1 h57 kb_1349_468
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 471 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 469 2 h58 kb_1349_469
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 471 1 h59 kb_1349_471
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 472 2 h60 kb_1349_472
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 474 6 h61 kb_1349_474
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 480 2 h62 kb_1349_480
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 482 22 h63 kb_1349_482
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 505 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 504 1 h64 kb_1349_504
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 505 1 h65 kb_1349_505
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 506 3 h66 kb_1349_506
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 524 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 509 15 h67 kb_1349_509
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 524 8 h68 kb_1349_524
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 533 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 532 1 h69 kb_1349_532
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 533 19 h70 kb_1349_533
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 552 5 h71 kb_1349_552
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 557 1 h72 kb_1349_557
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 558 1 h73 kb_1349_558
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 559 1 h74 kb_1349_559
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 560 1 h75 kb_1349_560
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 561 3 h76 kb_1349_561
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 564 1 h77 kb_1349_564
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 565 1 h78 kb_1349_565
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 568 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 566 2 h79 kb_1349_566
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 570 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 568 2 h80 kb_1349_568
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 570 2 h81 kb_1349_570
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 572 3 h82 kb_1349_572
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 575 1 h83 kb_1349_575
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 576 3 h84 kb_1349_576
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 579 10 h85 kb_1349_579
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 589 7 h86 kb_1349_589
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 603 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 596 7 h87 kb_1349_596
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 607 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 603 4 h88 kb_1349_603
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 607 2 h89 kb_1349_607
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 609 2 h90 kb_1349_609
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 611 2 h91 kb_1349_611
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 615 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 613 2 h92 kb_1349_613
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 615 1 h93 kb_1349_615
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 617 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 616 1 h94 kb_1349_616
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 618 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 617 1 h95 kb_1349_617
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 618 2 h96 kb_1349_618
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 620 2 h97 kb_1349_620
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 624 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 622 2 h98 kb_1349_622
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 625 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 624 1 h99 kb_1349_624
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 629 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 625 4 h100 kb_1349_625
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 634 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 629 5 h101 kb_1349_629
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 634 19 h102 kb_1349_634
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 653 5 h103 kb_1349_653
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 658 14 h104 kb_1349_658
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 672 11 h105 kb_1349_672
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 683 2 h106 kb_1349_683
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 685 14 h107 kb_1349_685
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 699 2 h108 kb_1349_699
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 701 6 h109 kb_1349_701
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 709 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 707 2 h110 kb_1349_707
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 709 21 h111 kb_1349_709
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 730 2 h112 kb_1349_730
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 732 7 h113 kb_1349_732
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 741 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 739 2 h114 kb_1349_739
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 762 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 741 21 h115 kb_1349_741
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 762 1 h116 kb_1349_762
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 765 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 763 2 h117 kb_1349_763
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 765 20 h118 kb_1349_765
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 795 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 785 10 h119 kb_1349_785
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 795 13 h120 kb_1349_795
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 810 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 808 2 h121 kb_1349_808
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 810 1 h122 kb_1349_810
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 816 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 811 5 h123 kb_1349_811
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 816 6 h124 kb_1349_816
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 822 4 h125 kb_1349_822
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 826 1 h126 kb_1349_826
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 836 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 827 9 h127 kb_1349_827
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 840 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 836 4 h128 kb_1349_836
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 840 1 h129 kb_1349_840
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 850 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 841 9 h130 kb_1349_841
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 852 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 850 2 h131 kb_1349_850
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 858 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 852 6 h132 kb_1349_852
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 859 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 858 1 h133 kb_1349_858
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 859 10 h134 kb_1349_859
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 872 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 869 3 h135 kb_1349_869
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 879 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 872 7 h136 kb_1349_872
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 887 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 879 8 h137 kb_1349_879
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 888 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 887 1 h138 kb_1349_887
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 894 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 888 6 h139 kb_1349_888
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 900 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 894 6 h140 kb_1349_894
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 900 3 h141 kb_1349_900
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 912 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 903 9 h142 kb_1349_903
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 927 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 912 15 h143 kb_1349_912
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 933 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 927 6 h144 kb_1349_927
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 933 2 h145 kb_1349_933
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 935 20 h146 kb_1349_935
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 957 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 955 2 h147 kb_1349_955
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 959 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 957 2 h148 kb_1349_957
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 963 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 959 4 h149 kb_1349_959
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 965 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 963 2 h150 kb_1349_963
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 985 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 965 20 h151 kb_1349_965
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 985 11 h152 kb_1349_985
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1008 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 996 12 h153 kb_1349_996
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1010 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1008 2 h154 kb_1349_1008
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1010 12 h155 kb_1349_1010
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1037 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1022 15 h156 kb_1349_1022
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1040 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1037 3 h157 kb_1349_1037
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1044 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1040 4 h158 kb_1349_1040
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1063 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1044 19 h159 kb_1349_1044
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1065 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1063 2 h160 kb_1349_1063
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1067 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1065 2 h161 kb_1349_1065
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1067 1 h162 kb_1349_1067
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1068 4 h163 kb_1349_1068
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1077 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1072 5 h164 kb_1349_1072
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1079 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1077 2 h165 kb_1349_1077
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1096 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1079 17 h166 kb_1349_1079
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1096 7 h167 kb_1349_1096
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1103 18 h168 kb_1349_1103
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1121 2 h169 kb_1349_1121
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1123 6 h170 kb_1349_1123
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1129 2 h171 kb_1349_1129
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1131 14 h172 kb_1349_1131
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1145 2 h173 kb_1349_1145
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1147 13 h174 kb_1349_1147
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1160 4 h175 kb_1349_1160
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1164 21 h176 kb_1349_1164
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1185 1 h177 kb_1349_1185
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1186 1 h178 kb_1349_1186
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1187 1 h179 kb_1349_1187
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1188 1 h180 kb_1349_1188
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1189 3 h181 kb_1349_1189
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1192 18 h182 kb_1349_1192
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1210 1 h183 kb_1349_1210
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1211 17 h184 kb_1349_1211
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1228 2 h185 kb_1349_1228
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1230 1 h186 kb_1349_1230
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1231 12 h187 kb_1349_1231
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1243 5 h188 kb_1349_1243
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1248 1 h189 kb_1349_1248
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1249 2 h190 kb_1349_1249
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1251 1 h191 kb_1349_1251
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1252 2 h192 kb_1349_1252
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1254 2 h193 kb_1349_1254
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1256 2 h194 kb_1349_1256
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1258 13 h195 kb_1349_1258
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1271 2 h196 kb_1349_1271
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1273 2 h197 kb_1349_1273
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1275 1 h198 kb_1349_1275
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1276 2 h199 kb_1349_1276
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1278 1 h200 kb_1349_1278
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1279 22 h201 kb_1349_1279
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1301 9 h202 kb_1349_1301
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1310 6 h203 kb_1349_1310
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1316 3 h204 kb_1349_1316
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1319 54 h205 kb_1349_1319
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1390 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1373 17 h206 kb_1349_1373
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1390 2 h207 kb_1349_1390
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1392 19 h208 kb_1349_1392
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1411 20 h209 kb_1349_1411
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1431 8 h210 kb_1349_1431
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1439 4 h211 kb_1349_1439
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1443 21 h212 kb_1349_1443
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1464 16 h213 kb_1349_1464
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1480 5 h214 kb_1349_1480
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1485 2 h215 kb_1349_1485
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1487 17 h216 kb_1349_1487
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1512 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1504 8 h217 kb_1349_1504
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1527 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1512 15 h218 kb_1349_1512
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1532 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1527 5 h219 kb_1349_1527
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1534 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1532 2 h220 kb_1349_1532
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1547 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1534 13 h221 kb_1349_1534
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1547 28 h222 kb_1349_1547
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1578 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1575 3 h223 kb_1349_1575
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1582 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1578 4 h224 kb_1349_1578
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1582 14 h225 kb_1349_1582
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1596 4 h226 kb_1349_1596
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1620 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1600 20 h227 kb_1349_1600
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1641 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1620 21 h228 kb_1349_1620
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1651 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1641 10 h229 kb_1349_1641
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1651 6 h230 kb_1349_1651
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1659 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1657 2 h231 kb_1349_1657
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1659 22 h232 kb_1349_1659
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1731 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1681 50 h233 kb_1349_1681
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1731 8 h234 kb_1349_1731
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1746 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1739 7 h235 kb_1349_1739
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1756 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1746 10 h236 kb_1349_1746
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1763 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1756 7 h237 kb_1349_1756
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1773 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1763 10 h238 kb_1349_1763
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1773 5 h239 kb_1349_1773
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1778 7 h240 kb_1349_1778
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1785 11 h241 kb_1349_1785
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1796 1 h242 kb_1349_1796
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1802 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1797 5 h243 kb_1349_1797
    have h245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1802 6 h244 kb_1349_1802
    have h246 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1808 3 h245 kb_1349_1808
    have h247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1811 18 h246 kb_1349_1811
    have h248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1843 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1829 14 h247 kb_1349_1829
    have h249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1853 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1843 10 h248 kb_1349_1843
    have h250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1881 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1853 28 h249 kb_1349_1853
    have h251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1915 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1881 34 h250 kb_1349_1881
    have h252 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1951 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1915 36 h251 kb_1349_1915
    have h253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1954 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1951 3 h252 kb_1349_1951
    have h254 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1971 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1954 17 h253 kb_1349_1954
    have h255 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1971 3 h254 kb_1349_1971
    have h256 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1981 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1974 7 h255 kb_1349_1974
    have h257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1993 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1981 12 h256 kb_1349_1981
    have h258 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2006 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 1993 13 h257 kb_1349_1993
    have h259 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2016 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2006 10 h258 kb_1349_2006
    have h260 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2046 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2016 30 h259 kb_1349_2016
    have h261 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2046 26 h260 kb_1349_2046
    have h262 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2093 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2072 21 h261 kb_1349_2072
    have h263 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2093 10 h262 kb_1349_2093
    have h264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1349.lits.getD i 0)) 0 2103 14 h263 kb_1349_2103
    exact h264
  have hg : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2117 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 6 = true := kg_1349_0
    have h1 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 14 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 6 8 h0 kg_1349_6
    have h2 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 22 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 14 8 h1 kg_1349_14
    have h3 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 23 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 22 1 h2 kg_1349_22
    have h4 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 28 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 23 5 h3 kg_1349_23
    have h5 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 43 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 28 15 h4 kg_1349_28
    have h6 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 45 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 43 2 h5 kg_1349_43
    have h7 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 57 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 45 12 h6 kg_1349_45
    have h8 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 58 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 57 1 h7 kg_1349_57
    have h9 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 69 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 58 11 h8 kg_1349_58
    have h10 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 87 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 69 18 h9 kg_1349_69
    have h11 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 89 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 87 2 h10 kg_1349_87
    have h12 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 95 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 89 6 h11 kg_1349_89
    have h13 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 97 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 95 2 h12 kg_1349_95
    have h14 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 114 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 97 17 h13 kg_1349_97
    have h15 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 120 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 114 6 h14 kg_1349_114
    have h16 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 121 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 120 1 h15 kg_1349_120
    have h17 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 122 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 121 1 h16 kg_1349_121
    have h18 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 124 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 122 2 h17 kg_1349_122
    have h19 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 132 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 124 8 h18 kg_1349_124
    have h20 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 154 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 132 22 h19 kg_1349_132
    have h21 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 156 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 154 2 h20 kg_1349_154
    have h22 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 159 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 156 3 h21 kg_1349_156
    have h23 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 162 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 159 3 h22 kg_1349_159
    have h24 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 163 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 162 1 h23 kg_1349_162
    have h25 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 164 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 163 1 h24 kg_1349_163
    have h26 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 165 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 164 1 h25 kg_1349_164
    have h27 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 185 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 165 20 h26 kg_1349_165
    have h28 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 196 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 185 11 h27 kg_1349_185
    have h29 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 202 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 196 6 h28 kg_1349_196
    have h30 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 204 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 202 2 h29 kg_1349_202
    have h31 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 217 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 204 13 h30 kg_1349_204
    have h32 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 227 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 217 10 h31 kg_1349_217
    have h33 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 229 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 227 2 h32 kg_1349_227
    have h34 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 232 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 229 3 h33 kg_1349_229
    have h35 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 234 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 232 2 h34 kg_1349_232
    have h36 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 235 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 234 1 h35 kg_1349_234
    have h37 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 261 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 235 26 h36 kg_1349_235
    have h38 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 266 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 261 5 h37 kg_1349_261
    have h39 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 272 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 266 6 h38 kg_1349_266
    have h40 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 274 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 272 2 h39 kg_1349_272
    have h41 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 296 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 274 22 h40 kg_1349_274
    have h42 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 299 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 296 3 h41 kg_1349_296
    have h43 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 306 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 299 7 h42 kg_1349_299
    have h44 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 342 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 306 36 h43 kg_1349_306
    have h45 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 356 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 342 14 h44 kg_1349_342
    have h46 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 360 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 356 4 h45 kg_1349_356
    have h47 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 372 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 360 12 h46 kg_1349_360
    have h48 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 387 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 372 15 h47 kg_1349_372
    have h49 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 389 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 387 2 h48 kg_1349_387
    have h50 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 401 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 389 12 h49 kg_1349_389
    have h51 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 413 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 401 12 h50 kg_1349_401
    have h52 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 421 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 413 8 h51 kg_1349_413
    have h53 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 435 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 421 14 h52 kg_1349_421
    have h54 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 442 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 435 7 h53 kg_1349_435
    have h55 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 445 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 442 3 h54 kg_1349_442
    have h56 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 467 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 445 22 h55 kg_1349_445
    have h57 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 468 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 467 1 h56 kg_1349_467
    have h58 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 469 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 468 1 h57 kg_1349_468
    have h59 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 471 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 469 2 h58 kg_1349_469
    have h60 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 472 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 471 1 h59 kg_1349_471
    have h61 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 474 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 472 2 h60 kg_1349_472
    have h62 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 480 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 474 6 h61 kg_1349_474
    have h63 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 482 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 480 2 h62 kg_1349_480
    have h64 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 504 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 482 22 h63 kg_1349_482
    have h65 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 505 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 504 1 h64 kg_1349_504
    have h66 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 506 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 505 1 h65 kg_1349_505
    have h67 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 509 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 506 3 h66 kg_1349_506
    have h68 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 524 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 509 15 h67 kg_1349_509
    have h69 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 532 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 524 8 h68 kg_1349_524
    have h70 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 533 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 532 1 h69 kg_1349_532
    have h71 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 552 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 533 19 h70 kg_1349_533
    have h72 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 557 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 552 5 h71 kg_1349_552
    have h73 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 558 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 557 1 h72 kg_1349_557
    have h74 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 559 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 558 1 h73 kg_1349_558
    have h75 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 560 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 559 1 h74 kg_1349_559
    have h76 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 561 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 560 1 h75 kg_1349_560
    have h77 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 564 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 561 3 h76 kg_1349_561
    have h78 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 565 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 564 1 h77 kg_1349_564
    have h79 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 566 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 565 1 h78 kg_1349_565
    have h80 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 568 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 566 2 h79 kg_1349_566
    have h81 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 570 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 568 2 h80 kg_1349_568
    have h82 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 572 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 570 2 h81 kg_1349_570
    have h83 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 575 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 572 3 h82 kg_1349_572
    have h84 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 576 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 575 1 h83 kg_1349_575
    have h85 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 579 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 576 3 h84 kg_1349_576
    have h86 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 589 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 579 10 h85 kg_1349_579
    have h87 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 596 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 589 7 h86 kg_1349_589
    have h88 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 603 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 596 7 h87 kg_1349_596
    have h89 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 607 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 603 4 h88 kg_1349_603
    have h90 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 609 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 607 2 h89 kg_1349_607
    have h91 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 611 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 609 2 h90 kg_1349_609
    have h92 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 613 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 611 2 h91 kg_1349_611
    have h93 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 615 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 613 2 h92 kg_1349_613
    have h94 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 616 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 615 1 h93 kg_1349_615
    have h95 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 617 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 616 1 h94 kg_1349_616
    have h96 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 618 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 617 1 h95 kg_1349_617
    have h97 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 620 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 618 2 h96 kg_1349_618
    have h98 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 622 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 620 2 h97 kg_1349_620
    have h99 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 624 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 622 2 h98 kg_1349_622
    have h100 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 625 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 624 1 h99 kg_1349_624
    have h101 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 629 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 625 4 h100 kg_1349_625
    have h102 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 634 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 629 5 h101 kg_1349_629
    have h103 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 653 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 634 19 h102 kg_1349_634
    have h104 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 658 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 653 5 h103 kg_1349_653
    have h105 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 672 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 658 14 h104 kg_1349_658
    have h106 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 683 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 672 11 h105 kg_1349_672
    have h107 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 685 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 683 2 h106 kg_1349_683
    have h108 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 699 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 685 14 h107 kg_1349_685
    have h109 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 701 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 699 2 h108 kg_1349_699
    have h110 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 707 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 701 6 h109 kg_1349_701
    have h111 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 709 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 707 2 h110 kg_1349_707
    have h112 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 730 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 709 21 h111 kg_1349_709
    have h113 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 732 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 730 2 h112 kg_1349_730
    have h114 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 739 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 732 7 h113 kg_1349_732
    have h115 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 741 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 739 2 h114 kg_1349_739
    have h116 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 762 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 741 21 h115 kg_1349_741
    have h117 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 763 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 762 1 h116 kg_1349_762
    have h118 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 765 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 763 2 h117 kg_1349_763
    have h119 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 785 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 765 20 h118 kg_1349_765
    have h120 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 795 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 785 10 h119 kg_1349_785
    have h121 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 808 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 795 13 h120 kg_1349_795
    have h122 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 810 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 808 2 h121 kg_1349_808
    have h123 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 811 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 810 1 h122 kg_1349_810
    have h124 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 816 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 811 5 h123 kg_1349_811
    have h125 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 822 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 816 6 h124 kg_1349_816
    have h126 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 826 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 822 4 h125 kg_1349_822
    have h127 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 827 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 826 1 h126 kg_1349_826
    have h128 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 836 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 827 9 h127 kg_1349_827
    have h129 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 840 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 836 4 h128 kg_1349_836
    have h130 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 841 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 840 1 h129 kg_1349_840
    have h131 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 850 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 841 9 h130 kg_1349_841
    have h132 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 852 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 850 2 h131 kg_1349_850
    have h133 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 858 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 852 6 h132 kg_1349_852
    have h134 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 859 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 858 1 h133 kg_1349_858
    have h135 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 869 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 859 10 h134 kg_1349_859
    have h136 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 872 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 869 3 h135 kg_1349_869
    have h137 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 879 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 872 7 h136 kg_1349_872
    have h138 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 887 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 879 8 h137 kg_1349_879
    have h139 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 888 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 887 1 h138 kg_1349_887
    have h140 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 894 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 888 6 h139 kg_1349_888
    have h141 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 900 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 894 6 h140 kg_1349_894
    have h142 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 903 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 900 3 h141 kg_1349_900
    have h143 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 912 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 903 9 h142 kg_1349_903
    have h144 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 927 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 912 15 h143 kg_1349_912
    have h145 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 933 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 927 6 h144 kg_1349_927
    have h146 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 935 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 933 2 h145 kg_1349_933
    have h147 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 955 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 935 20 h146 kg_1349_935
    have h148 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 957 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 955 2 h147 kg_1349_955
    have h149 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 959 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 957 2 h148 kg_1349_957
    have h150 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 963 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 959 4 h149 kg_1349_959
    have h151 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 965 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 963 2 h150 kg_1349_963
    have h152 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 985 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 965 20 h151 kg_1349_965
    have h153 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 996 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 985 11 h152 kg_1349_985
    have h154 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1008 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 996 12 h153 kg_1349_996
    have h155 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1010 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1008 2 h154 kg_1349_1008
    have h156 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1022 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1010 12 h155 kg_1349_1010
    have h157 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1037 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1022 15 h156 kg_1349_1022
    have h158 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1040 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1037 3 h157 kg_1349_1037
    have h159 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1044 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1040 4 h158 kg_1349_1040
    have h160 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1063 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1044 19 h159 kg_1349_1044
    have h161 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1065 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1063 2 h160 kg_1349_1063
    have h162 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1067 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1065 2 h161 kg_1349_1065
    have h163 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1068 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1067 1 h162 kg_1349_1067
    have h164 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1072 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1068 4 h163 kg_1349_1068
    have h165 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1077 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1072 5 h164 kg_1349_1072
    have h166 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1079 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1077 2 h165 kg_1349_1077
    have h167 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1096 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1079 17 h166 kg_1349_1079
    have h168 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1103 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1096 7 h167 kg_1349_1096
    have h169 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1121 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1103 18 h168 kg_1349_1103
    have h170 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1123 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1121 2 h169 kg_1349_1121
    have h171 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1129 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1123 6 h170 kg_1349_1123
    have h172 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1131 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1129 2 h171 kg_1349_1129
    have h173 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1145 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1131 14 h172 kg_1349_1131
    have h174 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1147 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1145 2 h173 kg_1349_1145
    have h175 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1160 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1147 13 h174 kg_1349_1147
    have h176 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1164 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1160 4 h175 kg_1349_1160
    have h177 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1185 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1164 21 h176 kg_1349_1164
    have h178 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1186 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1185 1 h177 kg_1349_1185
    have h179 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1187 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1186 1 h178 kg_1349_1186
    have h180 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1188 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1187 1 h179 kg_1349_1187
    have h181 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1189 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1188 1 h180 kg_1349_1188
    have h182 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1192 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1189 3 h181 kg_1349_1189
    have h183 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1210 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1192 18 h182 kg_1349_1192
    have h184 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1211 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1210 1 h183 kg_1349_1210
    have h185 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1228 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1211 17 h184 kg_1349_1211
    have h186 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1230 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1228 2 h185 kg_1349_1228
    have h187 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1231 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1230 1 h186 kg_1349_1230
    have h188 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1243 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1231 12 h187 kg_1349_1231
    have h189 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1248 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1243 5 h188 kg_1349_1243
    have h190 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1249 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1248 1 h189 kg_1349_1248
    have h191 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1251 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1249 2 h190 kg_1349_1249
    have h192 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1252 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1251 1 h191 kg_1349_1251
    have h193 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1254 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1252 2 h192 kg_1349_1252
    have h194 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1256 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1254 2 h193 kg_1349_1254
    have h195 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1258 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1256 2 h194 kg_1349_1256
    have h196 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1271 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1258 13 h195 kg_1349_1258
    have h197 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1273 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1271 2 h196 kg_1349_1271
    have h198 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1275 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1273 2 h197 kg_1349_1273
    have h199 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1276 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1275 1 h198 kg_1349_1275
    have h200 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1278 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1276 2 h199 kg_1349_1276
    have h201 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1279 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1278 1 h200 kg_1349_1278
    have h202 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1301 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1279 22 h201 kg_1349_1279
    have h203 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1310 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1301 9 h202 kg_1349_1301
    have h204 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1316 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1310 6 h203 kg_1349_1310
    have h205 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1319 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1316 3 h204 kg_1349_1316
    have h206 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1373 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1319 54 h205 kg_1349_1319
    have h207 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1390 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1373 17 h206 kg_1349_1373
    have h208 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1392 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1390 2 h207 kg_1349_1390
    have h209 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1411 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1392 19 h208 kg_1349_1392
    have h210 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1431 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1411 20 h209 kg_1349_1411
    have h211 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1439 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1431 8 h210 kg_1349_1431
    have h212 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1443 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1439 4 h211 kg_1349_1439
    have h213 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1464 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1443 21 h212 kg_1349_1443
    have h214 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1480 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1464 16 h213 kg_1349_1464
    have h215 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1485 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1480 5 h214 kg_1349_1480
    have h216 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1487 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1485 2 h215 kg_1349_1485
    have h217 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1504 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1487 17 h216 kg_1349_1487
    have h218 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1512 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1504 8 h217 kg_1349_1504
    have h219 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1527 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1512 15 h218 kg_1349_1512
    have h220 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1532 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1527 5 h219 kg_1349_1527
    have h221 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1534 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1532 2 h220 kg_1349_1532
    have h222 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1547 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1534 13 h221 kg_1349_1534
    have h223 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1575 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1547 28 h222 kg_1349_1547
    have h224 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1578 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1575 3 h223 kg_1349_1575
    have h225 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1582 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1578 4 h224 kg_1349_1578
    have h226 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1596 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1582 14 h225 kg_1349_1582
    have h227 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1600 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1596 4 h226 kg_1349_1596
    have h228 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1620 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1600 20 h227 kg_1349_1600
    have h229 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1641 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1620 21 h228 kg_1349_1620
    have h230 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1651 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1641 10 h229 kg_1349_1641
    have h231 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1657 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1651 6 h230 kg_1349_1651
    have h232 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1659 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1657 2 h231 kg_1349_1657
    have h233 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1681 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1659 22 h232 kg_1349_1659
    have h234 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1731 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1681 50 h233 kg_1349_1681
    have h235 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1739 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1731 8 h234 kg_1349_1731
    have h236 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1746 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1739 7 h235 kg_1349_1739
    have h237 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1756 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1746 10 h236 kg_1349_1746
    have h238 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1763 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1756 7 h237 kg_1349_1756
    have h239 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1773 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1763 10 h238 kg_1349_1763
    have h240 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1778 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1773 5 h239 kg_1349_1773
    have h241 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1785 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1778 7 h240 kg_1349_1778
    have h242 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1796 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1785 11 h241 kg_1349_1785
    have h243 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1797 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1796 1 h242 kg_1349_1796
    have h244 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1802 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1797 5 h243 kg_1349_1797
    have h245 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1808 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1802 6 h244 kg_1349_1802
    have h246 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1811 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1808 3 h245 kg_1349_1808
    have h247 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1829 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1811 18 h246 kg_1349_1811
    have h248 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1843 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1829 14 h247 kg_1349_1829
    have h249 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1853 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1843 10 h248 kg_1349_1843
    have h250 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1881 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1853 28 h249 kg_1349_1853
    have h251 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1915 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1881 34 h250 kg_1349_1881
    have h252 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1951 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1915 36 h251 kg_1349_1915
    have h253 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1954 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1951 3 h252 kg_1349_1951
    have h254 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1971 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1954 17 h253 kg_1349_1954
    have h255 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1974 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1971 3 h254 kg_1349_1971
    have h256 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1981 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1974 7 h255 kg_1349_1974
    have h257 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 1993 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1981 12 h256 kg_1349_1981
    have h258 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2006 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 1993 13 h257 kg_1349_1993
    have h259 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2016 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2006 10 h258 kg_1349_2006
    have h260 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2046 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2016 30 h259 kg_1349_2016
    have h261 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2072 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2046 26 h260 kg_1349_2046
    have h262 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2093 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2072 21 h261 kg_1349_2072
    have h263 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2103 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2093 10 h262 kg_1349_2093
    have h264 : IPChk.allR (Pts.glueIB K1349.lits KW_1349) 0 2117 = true := IPChk.allR_join (Pts.glueIB K1349.lits KW_1349) 0 2103 14 h263 kg_1349_2103
    exact h264
  have hlen : K1349.lits.length = 2117 := by decide
  intro k h1 h2
  obtain rfl : k = 1349 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1349) K1349.lits KW_1349
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_281 : ∀ k, 1350 ≤ k → k < 1352 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1350 JW_1350 1350 2 jr_1350
theorem jr6_282 : ∀ k, 1352 ≤ k → k < 1353 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 575 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 3 = true := kb_1352_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 3 16 h0 kb_1352_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 19 9 h1 kb_1352_19
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 28 1 h2 kb_1352_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 29 3 h3 kb_1352_29
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 87 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 32 55 h4 kb_1352_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 87 2 h5 kb_1352_87
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 89 30 h6 kb_1352_89
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 119 12 h7 kb_1352_119
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 131 4 h8 kb_1352_131
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 135 20 h9 kb_1352_135
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 155 8 h10 kb_1352_155
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 163 18 h11 kb_1352_163
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 181 12 h12 kb_1352_181
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 193 14 h13 kb_1352_193
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 207 1 h14 kb_1352_207
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 208 17 h15 kb_1352_208
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 225 36 h16 kb_1352_225
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 261 2 h17 kb_1352_261
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 263 6 h18 kb_1352_263
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 271 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 269 2 h19 kb_1352_269
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 271 20 h20 kb_1352_271
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 291 1 h21 kb_1352_291
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 292 4 h22 kb_1352_292
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 296 2 h23 kb_1352_296
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 298 21 h24 kb_1352_298
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 319 34 h25 kb_1352_319
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 353 30 h26 kb_1352_353
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 400 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 383 17 h27 kb_1352_383
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 400 4 h28 kb_1352_400
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 404 28 h29 kb_1352_404
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 432 12 h30 kb_1352_432
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 444 3 h31 kb_1352_444
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 463 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 447 16 h32 kb_1352_447
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 463 13 h33 kb_1352_463
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 476 9 h34 kb_1352_476
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 485 35 h35 kb_1352_485
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 520 44 h36 kb_1352_520
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1352.lits.getD i 0)) 0 564 11 h37 kb_1352_564
    exact h38
  have hg : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 575 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 3 = true := kg_1352_0
    have h1 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 19 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 3 16 h0 kg_1352_3
    have h2 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 28 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 19 9 h1 kg_1352_19
    have h3 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 29 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 28 1 h2 kg_1352_28
    have h4 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 32 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 29 3 h3 kg_1352_29
    have h5 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 87 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 32 55 h4 kg_1352_32
    have h6 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 89 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 87 2 h5 kg_1352_87
    have h7 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 119 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 89 30 h6 kg_1352_89
    have h8 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 131 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 119 12 h7 kg_1352_119
    have h9 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 135 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 131 4 h8 kg_1352_131
    have h10 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 155 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 135 20 h9 kg_1352_135
    have h11 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 163 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 155 8 h10 kg_1352_155
    have h12 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 181 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 163 18 h11 kg_1352_163
    have h13 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 193 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 181 12 h12 kg_1352_181
    have h14 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 207 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 193 14 h13 kg_1352_193
    have h15 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 208 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 207 1 h14 kg_1352_207
    have h16 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 225 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 208 17 h15 kg_1352_208
    have h17 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 261 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 225 36 h16 kg_1352_225
    have h18 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 263 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 261 2 h17 kg_1352_261
    have h19 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 269 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 263 6 h18 kg_1352_263
    have h20 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 271 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 269 2 h19 kg_1352_269
    have h21 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 291 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 271 20 h20 kg_1352_271
    have h22 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 292 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 291 1 h21 kg_1352_291
    have h23 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 296 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 292 4 h22 kg_1352_292
    have h24 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 298 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 296 2 h23 kg_1352_296
    have h25 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 319 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 298 21 h24 kg_1352_298
    have h26 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 353 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 319 34 h25 kg_1352_319
    have h27 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 383 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 353 30 h26 kg_1352_353
    have h28 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 400 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 383 17 h27 kg_1352_383
    have h29 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 404 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 400 4 h28 kg_1352_400
    have h30 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 432 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 404 28 h29 kg_1352_404
    have h31 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 444 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 432 12 h30 kg_1352_432
    have h32 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 447 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 444 3 h31 kg_1352_444
    have h33 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 463 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 447 16 h32 kg_1352_447
    have h34 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 476 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 463 13 h33 kg_1352_463
    have h35 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 485 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 476 9 h34 kg_1352_476
    have h36 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 520 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 485 35 h35 kg_1352_485
    have h37 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 564 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 520 44 h36 kg_1352_520
    have h38 : IPChk.allR (Pts.glueIB K1352.lits KW_1352) 0 575 = true := IPChk.allR_join (Pts.glueIB K1352.lits KW_1352) 0 564 11 h37 kg_1352_564
    exact h38
  have hlen : K1352.lits.length = 575 := by decide
  intro k h1 h2
  obtain rfl : k = 1352 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1352) K1352.lits KW_1352
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_283 : ∀ k, 1353 ≤ k → k < 1354 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 427 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 2 = true := kb_1353_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 2 14 h0 kb_1353_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 16 6 h1 kb_1353_16
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 22 30 h2 kb_1353_22
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 52 25 h3 kb_1353_52
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 77 12 h4 kb_1353_77
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 89 4 h5 kb_1353_89
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 93 11 h6 kb_1353_93
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 104 15 h7 kb_1353_104
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 119 2 h8 kb_1353_119
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 121 13 h9 kb_1353_121
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 134 15 h10 kb_1353_134
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 149 2 h11 kb_1353_149
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 151 14 h12 kb_1353_151
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 165 1 h13 kb_1353_165
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 166 1 h14 kb_1353_166
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 167 17 h15 kb_1353_167
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 184 7 h16 kb_1353_184
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 191 6 h17 kb_1353_191
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 197 2 h18 kb_1353_197
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 199 13 h19 kb_1353_199
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 212 2 h20 kb_1353_212
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 214 4 h21 kb_1353_214
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 218 2 h22 kb_1353_218
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 220 20 h23 kb_1353_220
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 240 18 h24 kb_1353_240
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 258 10 h25 kb_1353_258
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 268 31 h26 kb_1353_268
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 299 2 h27 kb_1353_299
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 306 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 301 5 h28 kb_1353_301
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 308 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 306 2 h29 kb_1353_306
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 308 14 h30 kb_1353_308
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 322 28 h31 kb_1353_322
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 350 9 h32 kb_1353_350
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 359 7 h33 kb_1353_359
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 390 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 366 24 h34 kb_1353_366
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 390 13 h35 kb_1353_390
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 403 9 h36 kb_1353_403
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1353.lits.getD i 0)) 0 412 15 h37 kb_1353_412
    exact h38
  have hg : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 427 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 2 = true := kg_1353_0
    have h1 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 16 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 2 14 h0 kg_1353_2
    have h2 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 22 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 16 6 h1 kg_1353_16
    have h3 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 52 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 22 30 h2 kg_1353_22
    have h4 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 77 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 52 25 h3 kg_1353_52
    have h5 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 89 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 77 12 h4 kg_1353_77
    have h6 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 93 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 89 4 h5 kg_1353_89
    have h7 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 104 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 93 11 h6 kg_1353_93
    have h8 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 119 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 104 15 h7 kg_1353_104
    have h9 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 121 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 119 2 h8 kg_1353_119
    have h10 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 134 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 121 13 h9 kg_1353_121
    have h11 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 149 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 134 15 h10 kg_1353_134
    have h12 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 151 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 149 2 h11 kg_1353_149
    have h13 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 165 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 151 14 h12 kg_1353_151
    have h14 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 166 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 165 1 h13 kg_1353_165
    have h15 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 167 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 166 1 h14 kg_1353_166
    have h16 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 184 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 167 17 h15 kg_1353_167
    have h17 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 191 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 184 7 h16 kg_1353_184
    have h18 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 197 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 191 6 h17 kg_1353_191
    have h19 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 199 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 197 2 h18 kg_1353_197
    have h20 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 212 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 199 13 h19 kg_1353_199
    have h21 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 214 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 212 2 h20 kg_1353_212
    have h22 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 218 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 214 4 h21 kg_1353_214
    have h23 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 220 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 218 2 h22 kg_1353_218
    have h24 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 240 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 220 20 h23 kg_1353_220
    have h25 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 258 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 240 18 h24 kg_1353_240
    have h26 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 268 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 258 10 h25 kg_1353_258
    have h27 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 299 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 268 31 h26 kg_1353_268
    have h28 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 301 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 299 2 h27 kg_1353_299
    have h29 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 306 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 301 5 h28 kg_1353_301
    have h30 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 308 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 306 2 h29 kg_1353_306
    have h31 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 322 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 308 14 h30 kg_1353_308
    have h32 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 350 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 322 28 h31 kg_1353_322
    have h33 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 359 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 350 9 h32 kg_1353_350
    have h34 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 366 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 359 7 h33 kg_1353_359
    have h35 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 390 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 366 24 h34 kg_1353_366
    have h36 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 403 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 390 13 h35 kg_1353_390
    have h37 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 412 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 403 9 h36 kg_1353_403
    have h38 : IPChk.allR (Pts.glueIB K1353.lits KW_1353) 0 427 = true := IPChk.allR_join (Pts.glueIB K1353.lits KW_1353) 0 412 15 h37 kg_1353_412
    exact h38
  have hlen : K1353.lits.length = 427 := by decide
  intro k h1 h2
  obtain rfl : k = 1353 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1353) K1353.lits KW_1353
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_284 : ∀ k, 1354 ≤ k → k < 1355 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1354 JW_1354 1354 1 jr_1354
theorem jr6_285 : ∀ k, 1355 ≤ k → k < 1356 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 907 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 1 = true := kb_1355_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 1 1 h0 kb_1355_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 2 1 h1 kb_1355_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 3 9 h2 kb_1355_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 12 20 h3 kb_1355_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 32 2 h4 kb_1355_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 34 6 h5 kb_1355_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 40 2 h6 kb_1355_40
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 42 18 h7 kb_1355_42
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 60 7 h8 kb_1355_60
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 67 6 h9 kb_1355_67
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 73 22 h10 kb_1355_73
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 95 2 h11 kb_1355_95
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 97 6 h12 kb_1355_97
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 103 13 h13 kb_1355_103
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 116 11 h14 kb_1355_116
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 127 5 h15 kb_1355_127
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 132 12 h16 kb_1355_132
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 144 15 h17 kb_1355_144
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 159 2 h18 kb_1355_159
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 161 14 h19 kb_1355_161
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 175 10 h20 kb_1355_175
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 185 7 h21 kb_1355_185
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 192 14 h22 kb_1355_192
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 206 2 h23 kb_1355_206
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 214 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 208 6 h24 kb_1355_208
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 214 2 h25 kb_1355_214
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 216 22 h26 kb_1355_216
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 238 1 h27 kb_1355_238
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 239 2 h28 kb_1355_239
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 241 9 h29 kb_1355_241
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 250 23 h30 kb_1355_250
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 273 1 h31 kb_1355_273
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 274 1 h32 kb_1355_274
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 275 3 h33 kb_1355_275
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 300 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 278 22 h34 kb_1355_278
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 300 1 h35 kb_1355_300
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 301 1 h36 kb_1355_301
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 303 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 302 1 h37 kb_1355_302
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 325 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 303 22 h38 kb_1355_303
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 325 1 h39 kb_1355_325
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 328 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 326 2 h40 kb_1355_326
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 329 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 328 1 h41 kb_1355_328
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 329 2 h42 kb_1355_329
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 336 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 331 5 h43 kb_1355_331
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 336 23 h44 kb_1355_336
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 359 2 h45 kb_1355_359
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 367 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 361 6 h46 kb_1355_361
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 367 2 h47 kb_1355_367
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 369 20 h48 kb_1355_369
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 391 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 389 2 h49 kb_1355_389
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 397 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 391 6 h50 kb_1355_391
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 397 22 h51 kb_1355_397
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 419 8 h52 kb_1355_419
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 442 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 427 15 h53 kb_1355_427
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 442 8 h54 kb_1355_442
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 466 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 450 16 h55 kb_1355_450
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 466 6 h56 kb_1355_466
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 496 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 472 24 h57 kb_1355_472
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 496 1 h58 kb_1355_496
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 499 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 497 2 h59 kb_1355_497
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 499 5 h60 kb_1355_499
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 506 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 504 2 h61 kb_1355_504
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 526 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 506 20 h62 kb_1355_506
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 526 24 h63 kb_1355_526
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 556 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 550 6 h64 kb_1355_550
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 556 2 h65 kb_1355_556
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 558 17 h66 kb_1355_558
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 575 27 h67 kb_1355_575
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 613 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 602 11 h68 kb_1355_602
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 616 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 613 3 h69 kb_1355_613
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 617 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 616 1 h70 kb_1355_616
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 619 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 617 2 h71 kb_1355_617
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 623 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 619 4 h72 kb_1355_619
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 623 19 h73 kb_1355_623
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 642 1 h74 kb_1355_642
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 645 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 643 2 h75 kb_1355_643
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 645 17 h76 kb_1355_645
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 662 2 h77 kb_1355_662
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 664 17 h78 kb_1355_664
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 681 2 h79 kb_1355_681
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 683 2 h80 kb_1355_683
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 685 2 h81 kb_1355_685
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 687 1 h82 kb_1355_687
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 688 1 h83 kb_1355_688
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 701 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 689 12 h84 kb_1355_689
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 716 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 701 15 h85 kb_1355_701
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 716 6 h86 kb_1355_716
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 750 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 722 28 h87 kb_1355_722
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 770 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 750 20 h88 kb_1355_750
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 800 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 770 30 h89 kb_1355_770
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 800 24 h90 kb_1355_800
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 824 31 h91 kb_1355_824
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 880 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 855 25 h92 kb_1355_855
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 888 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 880 8 h93 kb_1355_880
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 903 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 888 15 h94 kb_1355_888
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 907 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1355.lits.getD i 0)) 0 903 4 h95 kb_1355_903
    exact h96
  have hg : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 907 = true := by
    have h0 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 1 = true := kg_1355_0
    have h1 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 2 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 1 1 h0 kg_1355_1
    have h2 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 3 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 2 1 h1 kg_1355_2
    have h3 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 12 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 3 9 h2 kg_1355_3
    have h4 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 32 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 12 20 h3 kg_1355_12
    have h5 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 34 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 32 2 h4 kg_1355_32
    have h6 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 40 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 34 6 h5 kg_1355_34
    have h7 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 42 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 40 2 h6 kg_1355_40
    have h8 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 60 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 42 18 h7 kg_1355_42
    have h9 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 67 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 60 7 h8 kg_1355_60
    have h10 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 73 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 67 6 h9 kg_1355_67
    have h11 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 95 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 73 22 h10 kg_1355_73
    have h12 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 97 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 95 2 h11 kg_1355_95
    have h13 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 103 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 97 6 h12 kg_1355_97
    have h14 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 116 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 103 13 h13 kg_1355_103
    have h15 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 127 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 116 11 h14 kg_1355_116
    have h16 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 132 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 127 5 h15 kg_1355_127
    have h17 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 144 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 132 12 h16 kg_1355_132
    have h18 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 159 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 144 15 h17 kg_1355_144
    have h19 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 161 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 159 2 h18 kg_1355_159
    have h20 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 175 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 161 14 h19 kg_1355_161
    have h21 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 185 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 175 10 h20 kg_1355_175
    have h22 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 192 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 185 7 h21 kg_1355_185
    have h23 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 206 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 192 14 h22 kg_1355_192
    have h24 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 208 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 206 2 h23 kg_1355_206
    have h25 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 214 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 208 6 h24 kg_1355_208
    have h26 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 216 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 214 2 h25 kg_1355_214
    have h27 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 238 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 216 22 h26 kg_1355_216
    have h28 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 239 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 238 1 h27 kg_1355_238
    have h29 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 241 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 239 2 h28 kg_1355_239
    have h30 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 250 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 241 9 h29 kg_1355_241
    have h31 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 273 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 250 23 h30 kg_1355_250
    have h32 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 274 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 273 1 h31 kg_1355_273
    have h33 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 275 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 274 1 h32 kg_1355_274
    have h34 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 278 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 275 3 h33 kg_1355_275
    have h35 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 300 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 278 22 h34 kg_1355_278
    have h36 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 301 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 300 1 h35 kg_1355_300
    have h37 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 302 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 301 1 h36 kg_1355_301
    have h38 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 303 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 302 1 h37 kg_1355_302
    have h39 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 325 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 303 22 h38 kg_1355_303
    have h40 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 326 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 325 1 h39 kg_1355_325
    have h41 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 328 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 326 2 h40 kg_1355_326
    have h42 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 329 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 328 1 h41 kg_1355_328
    have h43 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 331 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 329 2 h42 kg_1355_329
    have h44 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 336 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 331 5 h43 kg_1355_331
    have h45 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 359 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 336 23 h44 kg_1355_336
    have h46 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 361 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 359 2 h45 kg_1355_359
    have h47 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 367 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 361 6 h46 kg_1355_361
    have h48 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 369 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 367 2 h47 kg_1355_367
    have h49 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 389 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 369 20 h48 kg_1355_369
    have h50 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 391 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 389 2 h49 kg_1355_389
    have h51 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 397 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 391 6 h50 kg_1355_391
    have h52 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 419 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 397 22 h51 kg_1355_397
    have h53 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 427 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 419 8 h52 kg_1355_419
    have h54 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 442 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 427 15 h53 kg_1355_427
    have h55 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 450 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 442 8 h54 kg_1355_442
    have h56 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 466 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 450 16 h55 kg_1355_450
    have h57 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 472 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 466 6 h56 kg_1355_466
    have h58 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 496 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 472 24 h57 kg_1355_472
    have h59 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 497 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 496 1 h58 kg_1355_496
    have h60 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 499 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 497 2 h59 kg_1355_497
    have h61 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 504 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 499 5 h60 kg_1355_499
    have h62 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 506 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 504 2 h61 kg_1355_504
    have h63 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 526 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 506 20 h62 kg_1355_506
    have h64 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 550 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 526 24 h63 kg_1355_526
    have h65 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 556 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 550 6 h64 kg_1355_550
    have h66 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 558 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 556 2 h65 kg_1355_556
    have h67 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 575 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 558 17 h66 kg_1355_558
    have h68 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 602 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 575 27 h67 kg_1355_575
    have h69 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 613 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 602 11 h68 kg_1355_602
    have h70 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 616 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 613 3 h69 kg_1355_613
    have h71 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 617 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 616 1 h70 kg_1355_616
    have h72 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 619 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 617 2 h71 kg_1355_617
    have h73 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 623 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 619 4 h72 kg_1355_619
    have h74 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 642 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 623 19 h73 kg_1355_623
    have h75 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 643 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 642 1 h74 kg_1355_642
    have h76 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 645 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 643 2 h75 kg_1355_643
    have h77 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 662 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 645 17 h76 kg_1355_645
    have h78 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 664 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 662 2 h77 kg_1355_662
    have h79 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 681 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 664 17 h78 kg_1355_664
    have h80 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 683 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 681 2 h79 kg_1355_681
    have h81 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 685 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 683 2 h80 kg_1355_683
    have h82 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 687 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 685 2 h81 kg_1355_685
    have h83 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 688 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 687 1 h82 kg_1355_687
    have h84 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 689 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 688 1 h83 kg_1355_688
    have h85 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 701 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 689 12 h84 kg_1355_689
    have h86 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 716 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 701 15 h85 kg_1355_701
    have h87 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 722 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 716 6 h86 kg_1355_716
    have h88 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 750 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 722 28 h87 kg_1355_722
    have h89 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 770 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 750 20 h88 kg_1355_750
    have h90 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 800 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 770 30 h89 kg_1355_770
    have h91 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 824 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 800 24 h90 kg_1355_800
    have h92 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 855 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 824 31 h91 kg_1355_824
    have h93 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 880 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 855 25 h92 kg_1355_855
    have h94 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 888 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 880 8 h93 kg_1355_880
    have h95 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 903 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 888 15 h94 kg_1355_888
    have h96 : IPChk.allR (Pts.glueIB K1355.lits KW_1355) 0 907 = true := IPChk.allR_join (Pts.glueIB K1355.lits KW_1355) 0 903 4 h95 kg_1355_903
    exact h96
  have hlen : K1355.lits.length = 907 := by decide
  intro k h1 h2
  obtain rfl : k = 1355 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 1355) K1355.lits KW_1355
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_286 : ∀ k, 1356 ≤ k → k < 1406 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_1356 JW_1356 1356 50 jr_1356

theorem grp6_10 : ∀ k, 1347 ≤ k → k < 1406 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_278
  have a1 := Pts.fa_join a0 jr6_279
  have a2 := Pts.fa_join a1 jr6_280
  have a3 := Pts.fa_join a2 jr6_281
  have a4 := Pts.fa_join a3 jr6_282
  have a5 := Pts.fa_join a4 jr6_283
  have a6 := Pts.fa_join a5 jr6_284
  have a7 := Pts.fa_join a6 jr6_285
  have a8 := Pts.fa_join a7 jr6_286
  exact a8

end B334.E1x.Pts.S707
