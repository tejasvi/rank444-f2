import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J115
import B334.E1x.Pts.S707.J118
import B334.E1x.Pts.S707.J155
import B334.E1x.Pts.S707.J157
import B334.E1x.Pts.S707.J159
import B334.E1x.Pts.S707.J165
import B334.E1x.Pts.S707.J175
import B334.E1x.Pts.S707.J183
import B334.E1x.Pts.S707.J189
import B334.E1x.Pts.S707.J237
import B334.E1x.Pts.S707.J239
import B334.E1x.Pts.S707.J244
import B334.E1x.Pts.S707.J246
import B334.E1x.Pts.S707.J248
import B334.E1x.Pts.S707.J263
import B334.E1x.Pts.S707.J265
import B334.E1x.Pts.S707.J268
import B334.E1x.Pts.S707.K113L
import B334.E1x.Pts.S707.K114L
import B334.E1x.Pts.S707.K117L
import B334.E1x.Pts.S707.K154L
import B334.E1x.Pts.S707.K156L
import B334.E1x.Pts.S707.K158L
import B334.E1x.Pts.S707.K164L
import B334.E1x.Pts.S707.K173L
import B334.E1x.Pts.S707.K174L
import B334.E1x.Pts.S707.K182L
import B334.E1x.Pts.S707.K188L
import B334.E1x.Pts.S707.K236L
import B334.E1x.Pts.S707.K238L
import B334.E1x.Pts.S707.K243L
import B334.E1x.Pts.S707.K245L
import B334.E1x.Pts.S707.K247L
import B334.E1x.Pts.S707.K262L
import B334.E1x.Pts.S707.K264L
import B334.E1x.Pts.S707.K267L
import B334.E1x.Pts.S707.K113Q0
import B334.E1x.Pts.S707.K113Q1
import B334.E1x.Pts.S707.K113Q2
import B334.E1x.Pts.S707.K113Q3
import B334.E1x.Pts.S707.K114C0
import B334.E1x.Pts.S707.K117Q0
import B334.E1x.Pts.S707.K117Q1
import B334.E1x.Pts.S707.K117Q2
import B334.E1x.Pts.S707.K117Q3
import B334.E1x.Pts.S707.K117Q4
import B334.E1x.Pts.S707.K117Q5
import B334.E1x.Pts.S707.K117Q6
import B334.E1x.Pts.S707.K117Q7
import B334.E1x.Pts.S707.K154C0
import B334.E1x.Pts.S707.K154C1
import B334.E1x.Pts.S707.K154C2
import B334.E1x.Pts.S707.K154C3
import B334.E1x.Pts.S707.K156C0
import B334.E1x.Pts.S707.K156C1
import B334.E1x.Pts.S707.K158C0
import B334.E1x.Pts.S707.K164C0
import B334.E1x.Pts.S707.K173C0
import B334.E1x.Pts.S707.K174Q0
import B334.E1x.Pts.S707.K174Q1
import B334.E1x.Pts.S707.K174Q2
import B334.E1x.Pts.S707.K174Q3
import B334.E1x.Pts.S707.K182C0
import B334.E1x.Pts.S707.K188C0
import B334.E1x.Pts.S707.K236C0
import B334.E1x.Pts.S707.K236C1
import B334.E1x.Pts.S707.K238C0
import B334.E1x.Pts.S707.K243C0
import B334.E1x.Pts.S707.K245C0
import B334.E1x.Pts.S707.K247C0
import B334.E1x.Pts.S707.K262C0
import B334.E1x.Pts.S707.K262C1
import B334.E1x.Pts.S707.K264C0
import B334.E1x.Pts.S707.K267C0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 113 … 286 (stage707_v6): the v5 Fin's job blocks r21 … r63 as
theorems, joined into `grp6_1` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_21 : ∀ k, 113 ≤ k → k < 114 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 299 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 3 = true := kb_113_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 3 23 h0 kb_113_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 26 9 h1 kb_113_26
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 35 20 h2 kb_113_35
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 55 22 h3 kb_113_55
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 77 7 h4 kb_113_77
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 84 6 h5 kb_113_84
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 90 13 h6 kb_113_90
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 103 2 h7 kb_113_103
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 105 13 h8 kb_113_105
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 118 7 h9 kb_113_118
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 125 14 h10 kb_113_125
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 139 2 h11 kb_113_139
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 141 15 h12 kb_113_141
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 156 2 h13 kb_113_156
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 158 1 h14 kb_113_158
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 159 11 h15 kb_113_159
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 170 11 h16 kb_113_170
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 181 2 h17 kb_113_181
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 183 1 h18 kb_113_183
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 184 4 h19 kb_113_184
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 188 8 h20 kb_113_188
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 196 22 h21 kb_113_196
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 218 5 h22 kb_113_218
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 223 5 h23 kb_113_223
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 228 21 h24 kb_113_228
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 249 5 h25 kb_113_249
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 254 13 h26 kb_113_254
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 267 3 h27 kb_113_267
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 270 2 h28 kb_113_270
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 272 1 h29 kb_113_272
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 273 2 h30 kb_113_273
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 279 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 275 4 h31 kb_113_275
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 280 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 279 1 h32 kb_113_279
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 280 1 h33 kb_113_280
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 281 5 h34 kb_113_281
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 288 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 286 2 h35 kb_113_286
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 293 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 288 5 h36 kb_113_288
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 294 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 293 1 h37 kb_113_293
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 294 2 h38 kb_113_294
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 296 2 h39 kb_113_296
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K113.lits.getD i 0)) 0 298 1 h40 kb_113_298
    exact h41
  have hg : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 299 = true := by
    have h0 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 3 = true := kg_113_0
    have h1 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 26 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 3 23 h0 kg_113_3
    have h2 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 35 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 26 9 h1 kg_113_26
    have h3 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 55 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 35 20 h2 kg_113_35
    have h4 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 77 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 55 22 h3 kg_113_55
    have h5 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 84 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 77 7 h4 kg_113_77
    have h6 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 90 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 84 6 h5 kg_113_84
    have h7 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 103 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 90 13 h6 kg_113_90
    have h8 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 105 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 103 2 h7 kg_113_103
    have h9 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 118 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 105 13 h8 kg_113_105
    have h10 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 125 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 118 7 h9 kg_113_118
    have h11 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 139 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 125 14 h10 kg_113_125
    have h12 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 141 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 139 2 h11 kg_113_139
    have h13 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 156 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 141 15 h12 kg_113_141
    have h14 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 158 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 156 2 h13 kg_113_156
    have h15 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 159 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 158 1 h14 kg_113_158
    have h16 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 170 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 159 11 h15 kg_113_159
    have h17 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 181 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 170 11 h16 kg_113_170
    have h18 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 183 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 181 2 h17 kg_113_181
    have h19 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 184 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 183 1 h18 kg_113_183
    have h20 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 188 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 184 4 h19 kg_113_184
    have h21 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 196 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 188 8 h20 kg_113_188
    have h22 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 218 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 196 22 h21 kg_113_196
    have h23 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 223 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 218 5 h22 kg_113_218
    have h24 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 228 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 223 5 h23 kg_113_223
    have h25 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 249 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 228 21 h24 kg_113_228
    have h26 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 254 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 249 5 h25 kg_113_249
    have h27 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 267 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 254 13 h26 kg_113_254
    have h28 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 270 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 267 3 h27 kg_113_267
    have h29 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 272 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 270 2 h28 kg_113_270
    have h30 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 273 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 272 1 h29 kg_113_272
    have h31 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 275 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 273 2 h30 kg_113_273
    have h32 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 279 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 275 4 h31 kg_113_275
    have h33 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 280 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 279 1 h32 kg_113_279
    have h34 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 281 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 280 1 h33 kg_113_280
    have h35 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 286 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 281 5 h34 kg_113_281
    have h36 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 288 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 286 2 h35 kg_113_286
    have h37 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 293 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 288 5 h36 kg_113_288
    have h38 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 294 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 293 1 h37 kg_113_293
    have h39 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 296 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 294 2 h38 kg_113_294
    have h40 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 298 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 296 2 h39 kg_113_296
    have h41 : IPChk.allR (Pts.glueIB K113.lits KW_113) 0 299 = true := IPChk.allR_join (Pts.glueIB K113.lits KW_113) 0 298 1 h40 kg_113_298
    exact h41
  have hlen : K113.lits.length = 299 := by decide
  intro k h1 h2
  obtain rfl : k = 113 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 113) K113.lits KW_113
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_22 : ∀ k, 114 ≤ k → k < 115 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 7 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 2 = true := kb_114_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 2 2 h0 kb_114_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 4 2 h1 kb_114_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K114.lits.getD i 0)) 0 6 1 h2 kb_114_6
    exact h3
  have hg : IPChk.allR (Pts.glueIB K114.lits KW_114) 0 7 = true := by
    have h0 : IPChk.allR (Pts.glueIB K114.lits KW_114) 0 2 = true := kg_114_0
    have h1 : IPChk.allR (Pts.glueIB K114.lits KW_114) 0 4 = true := IPChk.allR_join (Pts.glueIB K114.lits KW_114) 0 2 2 h0 kg_114_2
    have h2 : IPChk.allR (Pts.glueIB K114.lits KW_114) 0 6 = true := IPChk.allR_join (Pts.glueIB K114.lits KW_114) 0 4 2 h1 kg_114_4
    have h3 : IPChk.allR (Pts.glueIB K114.lits KW_114) 0 7 = true := IPChk.allR_join (Pts.glueIB K114.lits KW_114) 0 6 1 h2 kg_114_6
    exact h3
  have hlen : K114.lits.length = 7 := by decide
  intro k h1 h2
  obtain rfl : k = 114 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 114) K114.lits KW_114
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_23 : ∀ k, 115 ≤ k → k < 117 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_115 JW_115 115 2 jr_115
theorem jr6_24 : ∀ k, 117 ≤ k → k < 118 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 566 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 2 = true := kb_117_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 2 8 h0 kb_117_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 10 2 h1 kb_117_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 12 3 h2 kb_117_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 15 9 h3 kb_117_15
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 24 1 h4 kb_117_24
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 25 23 h5 kb_117_25
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 48 6 h6 kb_117_48
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 54 3 h7 kb_117_54
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 57 6 h8 kb_117_57
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 63 15 h9 kb_117_63
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 78 2 h10 kb_117_78
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 80 6 h11 kb_117_80
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 86 13 h12 kb_117_86
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 99 3 h13 kb_117_99
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 102 2 h14 kb_117_102
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 104 7 h15 kb_117_104
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 111 1 h16 kb_117_111
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 112 20 h17 kb_117_112
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 132 7 h18 kb_117_132
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 139 7 h19 kb_117_139
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 146 29 h20 kb_117_146
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 175 6 h21 kb_117_175
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 181 27 h22 kb_117_181
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 236 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 208 28 h23 kb_117_208
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 236 14 h24 kb_117_236
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 250 2 h25 kb_117_250
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 252 3 h26 kb_117_252
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 255 13 h27 kb_117_255
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 268 2 h28 kb_117_268
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 270 3 h29 kb_117_270
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 273 2 h30 kb_117_273
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 275 7 h31 kb_117_275
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 282 2 h32 kb_117_282
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 284 1 h33 kb_117_284
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 296 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 285 11 h34 kb_117_285
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 296 1 h35 kb_117_296
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 297 1 h36 kb_117_297
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 299 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 298 1 h37 kb_117_298
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 312 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 299 13 h38 kb_117_299
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 312 8 h39 kb_117_312
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 333 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 320 13 h40 kb_117_320
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 333 2 h41 kb_117_333
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 335 4 h42 kb_117_335
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 339 1 h43 kb_117_339
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 340 4 h44 kb_117_340
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 344 7 h45 kb_117_344
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 362 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 351 11 h46 kb_117_351
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 362 4 h47 kb_117_362
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 366 7 h48 kb_117_366
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 373 5 h49 kb_117_373
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 378 2 h50 kb_117_378
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 380 4 h51 kb_117_380
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 391 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 384 7 h52 kb_117_384
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 391 1 h53 kb_117_391
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 392 15 h54 kb_117_392
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 407 6 h55 kb_117_407
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 413 5 h56 kb_117_413
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 418 3 h57 kb_117_418
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 421 4 h58 kb_117_421
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 425 19 h59 kb_117_425
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 464 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 444 20 h60 kb_117_444
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 470 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 464 6 h61 kb_117_464
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 471 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 470 1 h62 kb_117_470
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 478 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 471 7 h63 kb_117_471
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 478 15 h64 kb_117_478
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 493 1 h65 kb_117_493
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 494 3 h66 kb_117_494
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 497 6 h67 kb_117_497
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 503 6 h68 kb_117_503
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 509 10 h69 kb_117_509
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 519 1 h70 kb_117_519
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 520 18 h71 kb_117_520
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 538 2 h72 kb_117_538
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 540 10 h73 kb_117_540
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 563 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 550 13 h74 kb_117_550
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 564 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 563 1 h75 kb_117_563
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 564 1 h76 kb_117_564
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K117.lits.getD i 0)) 0 565 1 h77 kb_117_565
    exact h78
  have hg : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 566 = true := by
    have h0 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 2 = true := kg_117_0
    have h1 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 10 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 2 8 h0 kg_117_2
    have h2 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 12 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 10 2 h1 kg_117_10
    have h3 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 15 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 12 3 h2 kg_117_12
    have h4 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 24 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 15 9 h3 kg_117_15
    have h5 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 25 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 24 1 h4 kg_117_24
    have h6 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 48 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 25 23 h5 kg_117_25
    have h7 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 54 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 48 6 h6 kg_117_48
    have h8 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 57 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 54 3 h7 kg_117_54
    have h9 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 63 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 57 6 h8 kg_117_57
    have h10 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 78 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 63 15 h9 kg_117_63
    have h11 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 80 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 78 2 h10 kg_117_78
    have h12 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 86 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 80 6 h11 kg_117_80
    have h13 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 99 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 86 13 h12 kg_117_86
    have h14 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 102 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 99 3 h13 kg_117_99
    have h15 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 104 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 102 2 h14 kg_117_102
    have h16 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 111 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 104 7 h15 kg_117_104
    have h17 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 112 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 111 1 h16 kg_117_111
    have h18 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 132 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 112 20 h17 kg_117_112
    have h19 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 139 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 132 7 h18 kg_117_132
    have h20 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 146 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 139 7 h19 kg_117_139
    have h21 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 175 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 146 29 h20 kg_117_146
    have h22 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 181 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 175 6 h21 kg_117_175
    have h23 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 208 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 181 27 h22 kg_117_181
    have h24 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 236 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 208 28 h23 kg_117_208
    have h25 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 250 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 236 14 h24 kg_117_236
    have h26 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 252 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 250 2 h25 kg_117_250
    have h27 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 255 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 252 3 h26 kg_117_252
    have h28 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 268 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 255 13 h27 kg_117_255
    have h29 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 270 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 268 2 h28 kg_117_268
    have h30 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 273 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 270 3 h29 kg_117_270
    have h31 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 275 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 273 2 h30 kg_117_273
    have h32 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 282 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 275 7 h31 kg_117_275
    have h33 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 284 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 282 2 h32 kg_117_282
    have h34 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 285 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 284 1 h33 kg_117_284
    have h35 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 296 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 285 11 h34 kg_117_285
    have h36 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 297 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 296 1 h35 kg_117_296
    have h37 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 298 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 297 1 h36 kg_117_297
    have h38 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 299 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 298 1 h37 kg_117_298
    have h39 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 312 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 299 13 h38 kg_117_299
    have h40 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 320 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 312 8 h39 kg_117_312
    have h41 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 333 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 320 13 h40 kg_117_320
    have h42 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 335 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 333 2 h41 kg_117_333
    have h43 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 339 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 335 4 h42 kg_117_335
    have h44 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 340 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 339 1 h43 kg_117_339
    have h45 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 344 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 340 4 h44 kg_117_340
    have h46 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 351 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 344 7 h45 kg_117_344
    have h47 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 362 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 351 11 h46 kg_117_351
    have h48 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 366 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 362 4 h47 kg_117_362
    have h49 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 373 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 366 7 h48 kg_117_366
    have h50 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 378 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 373 5 h49 kg_117_373
    have h51 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 380 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 378 2 h50 kg_117_378
    have h52 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 384 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 380 4 h51 kg_117_380
    have h53 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 391 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 384 7 h52 kg_117_384
    have h54 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 392 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 391 1 h53 kg_117_391
    have h55 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 407 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 392 15 h54 kg_117_392
    have h56 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 413 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 407 6 h55 kg_117_407
    have h57 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 418 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 413 5 h56 kg_117_413
    have h58 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 421 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 418 3 h57 kg_117_418
    have h59 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 425 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 421 4 h58 kg_117_421
    have h60 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 444 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 425 19 h59 kg_117_425
    have h61 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 464 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 444 20 h60 kg_117_444
    have h62 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 470 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 464 6 h61 kg_117_464
    have h63 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 471 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 470 1 h62 kg_117_470
    have h64 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 478 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 471 7 h63 kg_117_471
    have h65 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 493 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 478 15 h64 kg_117_478
    have h66 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 494 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 493 1 h65 kg_117_493
    have h67 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 497 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 494 3 h66 kg_117_494
    have h68 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 503 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 497 6 h67 kg_117_497
    have h69 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 509 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 503 6 h68 kg_117_503
    have h70 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 519 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 509 10 h69 kg_117_509
    have h71 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 520 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 519 1 h70 kg_117_519
    have h72 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 538 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 520 18 h71 kg_117_520
    have h73 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 540 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 538 2 h72 kg_117_538
    have h74 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 550 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 540 10 h73 kg_117_540
    have h75 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 563 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 550 13 h74 kg_117_550
    have h76 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 564 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 563 1 h75 kg_117_563
    have h77 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 565 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 564 1 h76 kg_117_564
    have h78 : IPChk.allR (Pts.glueIB K117.lits KW_117) 0 566 = true := IPChk.allR_join (Pts.glueIB K117.lits KW_117) 0 565 1 h77 kg_117_565
    exact h78
  have hlen : K117.lits.length = 566 := by decide
  intro k h1 h2
  obtain rfl : k = 117 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 117) K117.lits KW_117
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_25 : ∀ k, 118 ≤ k → k < 136 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_118 JW_118 118 18 jr_118
theorem jr6_26 : ∀ k, 136 ≤ k → k < 144 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_118 JW_118 136 8 jr_136
theorem jr6_27 : ∀ k, 144 ≤ k → k < 151 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_118 JW_118 144 7 jr_144
theorem jr6_28 : ∀ k, 151 ≤ k → k < 152 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_118 JW_118 151 1 jr_151
theorem jr6_29 : ∀ k, 152 ≤ k → k < 154 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_118 JW_118 152 2 jr_152
theorem jr6_30 : ∀ k, 154 ≤ k → k < 155 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1297 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 2 = true := kb_154_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 2 5 h0 kb_154_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 7 1 h1 kb_154_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 8 2 h2 kb_154_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 10 4 h3 kb_154_10
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 14 13 h4 kb_154_14
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 27 10 h5 kb_154_27
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 37 1 h6 kb_154_37
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 38 8 h7 kb_154_38
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 46 24 h8 kb_154_46
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 70 2 h9 kb_154_70
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 72 25 h10 kb_154_72
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 97 20 h11 kb_154_97
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 117 15 h12 kb_154_117
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 132 17 h13 kb_154_132
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 149 8 h14 kb_154_149
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 157 12 h15 kb_154_157
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 169 16 h16 kb_154_169
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 185 12 h17 kb_154_185
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 197 24 h18 kb_154_197
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 221 6 h19 kb_154_221
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 227 10 h20 kb_154_227
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 237 11 h21 kb_154_237
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 265 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 248 17 h22 kb_154_248
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 282 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 265 17 h23 kb_154_265
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 282 7 h24 kb_154_282
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 289 27 h25 kb_154_289
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 316 11 h26 kb_154_316
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 327 7 h27 kb_154_327
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 334 11 h28 kb_154_334
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 345 11 h29 kb_154_345
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 356 23 h30 kb_154_356
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 379 8 h31 kb_154_379
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 387 9 h32 kb_154_387
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 396 11 h33 kb_154_396
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 407 21 h34 kb_154_407
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 436 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 428 8 h35 kb_154_428
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 436 8 h36 kb_154_436
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 444 28 h37 kb_154_444
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 489 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 472 17 h38 kb_154_472
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 489 26 h39 kb_154_489
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 515 38 h40 kb_154_515
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 560 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 553 7 h41 kb_154_553
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 568 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 560 8 h42 kb_154_560
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 605 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 568 37 h43 kb_154_568
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 605 30 h44 kb_154_605
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 643 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 635 8 h45 kb_154_635
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 643 14 h46 kb_154_643
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 657 29 h47 kb_154_657
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 711 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 686 25 h48 kb_154_686
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 711 19 h49 kb_154_711
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 730 5 h50 kb_154_730
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 748 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 735 13 h51 kb_154_735
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 788 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 748 40 h52 kb_154_748
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 800 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 788 12 h53 kb_154_788
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 800 29 h54 kb_154_800
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 829 12 h55 kb_154_829
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 880 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 841 39 h56 kb_154_841
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 936 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 880 56 h57 kb_154_880
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 960 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 936 24 h58 kb_154_936
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 991 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 960 31 h59 kb_154_960
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1024 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 991 33 h60 kb_154_991
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1024 19 h61 kb_154_1024
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1090 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1043 47 h62 kb_154_1043
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1090 86 h63 kb_154_1090
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1176 24 h64 kb_154_1176
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1255 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1200 55 h65 kb_154_1200
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K154.lits.getD i 0)) 0 1255 42 h66 kb_154_1255
    exact h67
  have hg : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1297 = true := by
    have h0 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 2 = true := kg_154_0
    have h1 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 7 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 2 5 h0 kg_154_2
    have h2 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 8 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 7 1 h1 kg_154_7
    have h3 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 10 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 8 2 h2 kg_154_8
    have h4 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 14 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 10 4 h3 kg_154_10
    have h5 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 27 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 14 13 h4 kg_154_14
    have h6 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 37 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 27 10 h5 kg_154_27
    have h7 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 38 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 37 1 h6 kg_154_37
    have h8 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 46 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 38 8 h7 kg_154_38
    have h9 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 70 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 46 24 h8 kg_154_46
    have h10 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 72 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 70 2 h9 kg_154_70
    have h11 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 97 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 72 25 h10 kg_154_72
    have h12 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 117 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 97 20 h11 kg_154_97
    have h13 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 132 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 117 15 h12 kg_154_117
    have h14 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 149 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 132 17 h13 kg_154_132
    have h15 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 157 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 149 8 h14 kg_154_149
    have h16 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 169 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 157 12 h15 kg_154_157
    have h17 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 185 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 169 16 h16 kg_154_169
    have h18 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 197 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 185 12 h17 kg_154_185
    have h19 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 221 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 197 24 h18 kg_154_197
    have h20 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 227 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 221 6 h19 kg_154_221
    have h21 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 237 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 227 10 h20 kg_154_227
    have h22 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 248 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 237 11 h21 kg_154_237
    have h23 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 265 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 248 17 h22 kg_154_248
    have h24 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 282 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 265 17 h23 kg_154_265
    have h25 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 289 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 282 7 h24 kg_154_282
    have h26 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 316 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 289 27 h25 kg_154_289
    have h27 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 327 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 316 11 h26 kg_154_316
    have h28 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 334 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 327 7 h27 kg_154_327
    have h29 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 345 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 334 11 h28 kg_154_334
    have h30 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 356 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 345 11 h29 kg_154_345
    have h31 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 379 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 356 23 h30 kg_154_356
    have h32 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 387 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 379 8 h31 kg_154_379
    have h33 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 396 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 387 9 h32 kg_154_387
    have h34 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 407 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 396 11 h33 kg_154_396
    have h35 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 428 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 407 21 h34 kg_154_407
    have h36 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 436 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 428 8 h35 kg_154_428
    have h37 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 444 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 436 8 h36 kg_154_436
    have h38 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 472 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 444 28 h37 kg_154_444
    have h39 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 489 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 472 17 h38 kg_154_472
    have h40 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 515 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 489 26 h39 kg_154_489
    have h41 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 553 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 515 38 h40 kg_154_515
    have h42 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 560 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 553 7 h41 kg_154_553
    have h43 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 568 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 560 8 h42 kg_154_560
    have h44 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 605 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 568 37 h43 kg_154_568
    have h45 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 635 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 605 30 h44 kg_154_605
    have h46 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 643 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 635 8 h45 kg_154_635
    have h47 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 657 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 643 14 h46 kg_154_643
    have h48 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 686 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 657 29 h47 kg_154_657
    have h49 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 711 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 686 25 h48 kg_154_686
    have h50 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 730 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 711 19 h49 kg_154_711
    have h51 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 735 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 730 5 h50 kg_154_730
    have h52 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 748 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 735 13 h51 kg_154_735
    have h53 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 788 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 748 40 h52 kg_154_748
    have h54 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 800 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 788 12 h53 kg_154_788
    have h55 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 829 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 800 29 h54 kg_154_800
    have h56 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 841 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 829 12 h55 kg_154_829
    have h57 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 880 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 841 39 h56 kg_154_841
    have h58 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 936 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 880 56 h57 kg_154_880
    have h59 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 960 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 936 24 h58 kg_154_936
    have h60 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 991 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 960 31 h59 kg_154_960
    have h61 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1024 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 991 33 h60 kg_154_991
    have h62 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1043 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1024 19 h61 kg_154_1024
    have h63 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1090 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1043 47 h62 kg_154_1043
    have h64 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1176 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1090 86 h63 kg_154_1090
    have h65 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1200 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1176 24 h64 kg_154_1176
    have h66 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1255 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1200 55 h65 kg_154_1200
    have h67 : IPChk.allR (Pts.glueIB K154.lits KW_154) 0 1297 = true := IPChk.allR_join (Pts.glueIB K154.lits KW_154) 0 1255 42 h66 kg_154_1255
    exact h67
  have hlen : K154.lits.length = 1297 := by decide
  intro k h1 h2
  obtain rfl : k = 154 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 154) K154.lits KW_154
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_31 : ∀ k, 155 ≤ k → k < 156 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_155 JW_155 155 1 jr_155
theorem jr6_32 : ∀ k, 156 ≤ k → k < 157 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 631 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 2 = true := kb_156_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 2 5 h0 kb_156_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 7 9 h1 kb_156_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 16 8 h2 kb_156_16
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 24 4 h3 kb_156_24
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 28 8 h4 kb_156_28
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 36 17 h5 kb_156_36
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 53 6 h6 kb_156_53
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 59 8 h7 kb_156_59
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 67 13 h8 kb_156_67
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 80 46 h9 kb_156_80
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 126 13 h10 kb_156_126
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 139 21 h11 kb_156_139
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 160 5 h12 kb_156_160
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 165 8 h13 kb_156_165
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 173 26 h14 kb_156_173
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 199 13 h15 kb_156_199
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 212 22 h16 kb_156_212
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 289 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 234 55 h17 kb_156_234
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 304 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 289 15 h18 kb_156_289
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 346 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 304 42 h19 kb_156_304
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 346 36 h20 kb_156_346
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 401 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 382 19 h21 kb_156_382
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 401 2 h22 kb_156_401
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 417 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 403 14 h23 kb_156_403
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 417 90 h24 kb_156_417
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 507 60 h25 kb_156_507
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 567 22 h26 kb_156_567
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 626 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 589 37 h27 kb_156_589
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 631 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K156.lits.getD i 0)) 0 626 5 h28 kb_156_626
    exact h29
  have hg : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 631 = true := by
    have h0 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 2 = true := kg_156_0
    have h1 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 7 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 2 5 h0 kg_156_2
    have h2 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 16 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 7 9 h1 kg_156_7
    have h3 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 24 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 16 8 h2 kg_156_16
    have h4 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 28 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 24 4 h3 kg_156_24
    have h5 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 36 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 28 8 h4 kg_156_28
    have h6 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 53 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 36 17 h5 kg_156_36
    have h7 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 59 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 53 6 h6 kg_156_53
    have h8 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 67 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 59 8 h7 kg_156_59
    have h9 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 80 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 67 13 h8 kg_156_67
    have h10 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 126 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 80 46 h9 kg_156_80
    have h11 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 139 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 126 13 h10 kg_156_126
    have h12 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 160 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 139 21 h11 kg_156_139
    have h13 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 165 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 160 5 h12 kg_156_160
    have h14 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 173 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 165 8 h13 kg_156_165
    have h15 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 199 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 173 26 h14 kg_156_173
    have h16 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 212 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 199 13 h15 kg_156_199
    have h17 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 234 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 212 22 h16 kg_156_212
    have h18 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 289 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 234 55 h17 kg_156_234
    have h19 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 304 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 289 15 h18 kg_156_289
    have h20 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 346 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 304 42 h19 kg_156_304
    have h21 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 382 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 346 36 h20 kg_156_346
    have h22 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 401 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 382 19 h21 kg_156_382
    have h23 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 403 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 401 2 h22 kg_156_401
    have h24 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 417 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 403 14 h23 kg_156_403
    have h25 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 507 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 417 90 h24 kg_156_417
    have h26 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 567 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 507 60 h25 kg_156_507
    have h27 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 589 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 567 22 h26 kg_156_567
    have h28 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 626 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 589 37 h27 kg_156_589
    have h29 : IPChk.allR (Pts.glueIB K156.lits KW_156) 0 631 = true := IPChk.allR_join (Pts.glueIB K156.lits KW_156) 0 626 5 h28 kg_156_626
    exact h29
  have hlen : K156.lits.length = 631 := by decide
  intro k h1 h2
  obtain rfl : k = 156 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 156) K156.lits KW_156
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_33 : ∀ k, 157 ≤ k → k < 158 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_157 JW_157 157 1 jr_157
theorem jr6_34 : ∀ k, 158 ≤ k → k < 159 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K158.lits.getD i 0)) 0 50 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K158.lits.getD i 0)) 0 27 = true := kb_158_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K158.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K158.lits.getD i 0)) 0 27 23 h0 kb_158_27
    exact h1
  have hg : IPChk.allR (Pts.glueIB K158.lits KW_158) 0 50 = true := by
    have h0 : IPChk.allR (Pts.glueIB K158.lits KW_158) 0 27 = true := kg_158_0
    have h1 : IPChk.allR (Pts.glueIB K158.lits KW_158) 0 50 = true := IPChk.allR_join (Pts.glueIB K158.lits KW_158) 0 27 23 h0 kg_158_27
    exact h1
  have hlen : K158.lits.length = 50 := by decide
  intro k h1 h2
  obtain rfl : k = 158 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 158) K158.lits KW_158
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_35 : ∀ k, 159 ≤ k → k < 164 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_159 JW_159 159 5 jr_159
theorem jr6_36 : ∀ k, 164 ≤ k → k < 165 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 45 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 2 = true := kb_164_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 2 12 h0 kb_164_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K164.lits.getD i 0)) 0 14 31 h1 kb_164_14
    exact h2
  have hg : IPChk.allR (Pts.glueIB K164.lits KW_164) 0 45 = true := by
    have h0 : IPChk.allR (Pts.glueIB K164.lits KW_164) 0 2 = true := kg_164_0
    have h1 : IPChk.allR (Pts.glueIB K164.lits KW_164) 0 14 = true := IPChk.allR_join (Pts.glueIB K164.lits KW_164) 0 2 12 h0 kg_164_2
    have h2 : IPChk.allR (Pts.glueIB K164.lits KW_164) 0 45 = true := IPChk.allR_join (Pts.glueIB K164.lits KW_164) 0 14 31 h1 kg_164_14
    exact h2
  have hlen : K164.lits.length = 45 := by decide
  intro k h1 h2
  obtain rfl : k = 164 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 164) K164.lits KW_164
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_37 : ∀ k, 165 ≤ k → k < 173 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_165 JW_165 165 8 jr_165
theorem jr6_38 : ∀ k, 173 ≤ k → k < 174 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 145 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 1 = true := kb_173_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 1 6 h0 kb_173_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 7 17 h1 kb_173_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 24 57 h2 kb_173_24
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 81 56 h3 kb_173_81
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K173.lits.getD i 0)) 0 137 8 h4 kb_173_137
    exact h5
  have hg : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 145 = true := by
    have h0 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 1 = true := kg_173_0
    have h1 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 7 = true := IPChk.allR_join (Pts.glueIB K173.lits KW_173) 0 1 6 h0 kg_173_1
    have h2 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 24 = true := IPChk.allR_join (Pts.glueIB K173.lits KW_173) 0 7 17 h1 kg_173_7
    have h3 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 81 = true := IPChk.allR_join (Pts.glueIB K173.lits KW_173) 0 24 57 h2 kg_173_24
    have h4 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 137 = true := IPChk.allR_join (Pts.glueIB K173.lits KW_173) 0 81 56 h3 kg_173_81
    have h5 : IPChk.allR (Pts.glueIB K173.lits KW_173) 0 145 = true := IPChk.allR_join (Pts.glueIB K173.lits KW_173) 0 137 8 h4 kg_173_137
    exact h5
  have hlen : K173.lits.length = 145 := by decide
  intro k h1 h2
  obtain rfl : k = 173 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 173) K173.lits KW_173
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_39 : ∀ k, 174 ≤ k → k < 175 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 411 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 1 = true := kb_174_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 1 1 h0 kb_174_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 2 1 h1 kb_174_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 3 16 h2 kb_174_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 19 13 h3 kb_174_19
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 32 2 h4 kb_174_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 34 7 h5 kb_174_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 41 18 h6 kb_174_41
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 59 7 h7 kb_174_59
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 66 6 h8 kb_174_66
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 72 1 h9 kb_174_72
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 73 21 h10 kb_174_73
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 94 1 h11 kb_174_94
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 95 10 h12 kb_174_95
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 105 9 h13 kb_174_105
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 114 15 h14 kb_174_114
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 129 28 h15 kb_174_129
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 157 2 h16 kb_174_157
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 159 12 h17 kb_174_159
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 171 16 h18 kb_174_171
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 187 3 h19 kb_174_187
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 190 14 h20 kb_174_190
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 204 2 h21 kb_174_204
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 206 2 h22 kb_174_206
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 208 2 h23 kb_174_208
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 210 1 h24 kb_174_210
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 211 1 h25 kb_174_211
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 212 1 h26 kb_174_212
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 213 2 h27 kb_174_213
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 215 23 h28 kb_174_215
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 238 36 h29 kb_174_238
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 274 7 h30 kb_174_274
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 281 20 h31 kb_174_281
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 326 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 301 25 h32 kb_174_301
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 326 1 h33 kb_174_326
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 336 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 327 9 h34 kb_174_327
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 336 20 h35 kb_174_336
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 356 2 h36 kb_174_356
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 358 14 h37 kb_174_358
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 385 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 372 13 h38 kb_174_372
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 385 18 h39 kb_174_385
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K174.lits.getD i 0)) 0 403 8 h40 kb_174_403
    exact h41
  have hg : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 411 = true := by
    have h0 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 1 = true := kg_174_0
    have h1 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 2 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 1 1 h0 kg_174_1
    have h2 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 3 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 2 1 h1 kg_174_2
    have h3 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 19 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 3 16 h2 kg_174_3
    have h4 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 32 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 19 13 h3 kg_174_19
    have h5 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 34 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 32 2 h4 kg_174_32
    have h6 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 41 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 34 7 h5 kg_174_34
    have h7 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 59 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 41 18 h6 kg_174_41
    have h8 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 66 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 59 7 h7 kg_174_59
    have h9 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 72 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 66 6 h8 kg_174_66
    have h10 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 73 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 72 1 h9 kg_174_72
    have h11 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 94 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 73 21 h10 kg_174_73
    have h12 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 95 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 94 1 h11 kg_174_94
    have h13 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 105 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 95 10 h12 kg_174_95
    have h14 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 114 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 105 9 h13 kg_174_105
    have h15 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 129 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 114 15 h14 kg_174_114
    have h16 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 157 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 129 28 h15 kg_174_129
    have h17 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 159 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 157 2 h16 kg_174_157
    have h18 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 171 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 159 12 h17 kg_174_159
    have h19 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 187 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 171 16 h18 kg_174_171
    have h20 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 190 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 187 3 h19 kg_174_187
    have h21 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 204 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 190 14 h20 kg_174_190
    have h22 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 206 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 204 2 h21 kg_174_204
    have h23 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 208 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 206 2 h22 kg_174_206
    have h24 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 210 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 208 2 h23 kg_174_208
    have h25 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 211 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 210 1 h24 kg_174_210
    have h26 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 212 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 211 1 h25 kg_174_211
    have h27 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 213 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 212 1 h26 kg_174_212
    have h28 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 215 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 213 2 h27 kg_174_213
    have h29 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 238 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 215 23 h28 kg_174_215
    have h30 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 274 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 238 36 h29 kg_174_238
    have h31 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 281 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 274 7 h30 kg_174_274
    have h32 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 301 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 281 20 h31 kg_174_281
    have h33 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 326 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 301 25 h32 kg_174_301
    have h34 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 327 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 326 1 h33 kg_174_326
    have h35 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 336 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 327 9 h34 kg_174_327
    have h36 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 356 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 336 20 h35 kg_174_336
    have h37 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 358 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 356 2 h36 kg_174_356
    have h38 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 372 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 358 14 h37 kg_174_358
    have h39 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 385 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 372 13 h38 kg_174_372
    have h40 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 403 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 385 18 h39 kg_174_385
    have h41 : IPChk.allR (Pts.glueIB K174.lits KW_174) 0 411 = true := IPChk.allR_join (Pts.glueIB K174.lits KW_174) 0 403 8 h40 kg_174_403
    exact h41
  have hlen : K174.lits.length = 411 := by decide
  intro k h1 h2
  obtain rfl : k = 174 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 174) K174.lits KW_174
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_40 : ∀ k, 175 ≤ k → k < 182 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_175 JW_175 175 7 jr_175
theorem jr6_41 : ∀ k, 182 ≤ k → k < 183 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 6 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 1 = true := kb_182_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 1 2 h0 kb_182_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K182.lits.getD i 0)) 0 3 3 h1 kb_182_3
    exact h2
  have hg : IPChk.allR (Pts.glueIB K182.lits KW_182) 0 6 = true := by
    have h0 : IPChk.allR (Pts.glueIB K182.lits KW_182) 0 1 = true := kg_182_0
    have h1 : IPChk.allR (Pts.glueIB K182.lits KW_182) 0 3 = true := IPChk.allR_join (Pts.glueIB K182.lits KW_182) 0 1 2 h0 kg_182_1
    have h2 : IPChk.allR (Pts.glueIB K182.lits KW_182) 0 6 = true := IPChk.allR_join (Pts.glueIB K182.lits KW_182) 0 3 3 h1 kg_182_3
    exact h2
  have hlen : K182.lits.length = 6 := by decide
  intro k h1 h2
  obtain rfl : k = 182 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 182) K182.lits KW_182
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_42 : ∀ k, 183 ≤ k → k < 188 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_183 JW_183 183 5 jr_183
theorem jr6_43 : ∀ k, 188 ≤ k → k < 189 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K188.lits.getD i 0)) 0 9 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K188.lits.getD i 0)) 0 1 = true := kb_188_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K188.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K188.lits.getD i 0)) 0 1 8 h0 kb_188_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K188.lits KW_188) 0 9 = true := by
    have h0 : IPChk.allR (Pts.glueIB K188.lits KW_188) 0 1 = true := kg_188_0
    have h1 : IPChk.allR (Pts.glueIB K188.lits KW_188) 0 9 = true := IPChk.allR_join (Pts.glueIB K188.lits KW_188) 0 1 8 h0 kg_188_1
    exact h1
  have hlen : K188.lits.length = 9 := by decide
  intro k h1 h2
  obtain rfl : k = 188 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 188) K188.lits KW_188
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_44 : ∀ k, 189 ≤ k → k < 204 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_189 JW_189 189 15 jr_189
theorem jr6_45 : ∀ k, 204 ≤ k → k < 236 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_189 JW_189 204 32 jr_204
theorem jr6_46 : ∀ k, 236 ≤ k → k < 237 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 37 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 1 = true := kb_236_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 1 1 h0 kb_236_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 2 1 h1 kb_236_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 3 1 h2 kb_236_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 4 2 h3 kb_236_4
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 6 1 h4 kb_236_6
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 7 2 h5 kb_236_7
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 9 2 h6 kb_236_9
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 11 1 h7 kb_236_11
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 12 1 h8 kb_236_12
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 13 1 h9 kb_236_13
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 14 2 h10 kb_236_14
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 16 1 h11 kb_236_16
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 17 1 h12 kb_236_17
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 18 1 h13 kb_236_18
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 19 1 h14 kb_236_19
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 20 2 h15 kb_236_20
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 22 1 h16 kb_236_22
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 23 1 h17 kb_236_23
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 24 1 h18 kb_236_24
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 25 1 h19 kb_236_25
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 26 1 h20 kb_236_26
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 27 2 h21 kb_236_27
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 29 1 h22 kb_236_29
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 30 1 h23 kb_236_30
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 31 3 h24 kb_236_31
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 34 1 h25 kb_236_34
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 35 1 h26 kb_236_35
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K236.lits.getD i 0)) 0 36 1 h27 kb_236_36
    exact h28
  have hg : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 37 = true := by
    have h0 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 1 = true := kg_236_0
    have h1 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 2 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 1 1 h0 kg_236_1
    have h2 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 3 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 2 1 h1 kg_236_2
    have h3 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 4 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 3 1 h2 kg_236_3
    have h4 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 6 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 4 2 h3 kg_236_4
    have h5 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 7 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 6 1 h4 kg_236_6
    have h6 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 9 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 7 2 h5 kg_236_7
    have h7 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 11 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 9 2 h6 kg_236_9
    have h8 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 12 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 11 1 h7 kg_236_11
    have h9 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 13 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 12 1 h8 kg_236_12
    have h10 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 14 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 13 1 h9 kg_236_13
    have h11 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 16 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 14 2 h10 kg_236_14
    have h12 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 17 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 16 1 h11 kg_236_16
    have h13 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 18 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 17 1 h12 kg_236_17
    have h14 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 19 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 18 1 h13 kg_236_18
    have h15 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 20 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 19 1 h14 kg_236_19
    have h16 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 22 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 20 2 h15 kg_236_20
    have h17 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 23 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 22 1 h16 kg_236_22
    have h18 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 24 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 23 1 h17 kg_236_23
    have h19 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 25 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 24 1 h18 kg_236_24
    have h20 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 26 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 25 1 h19 kg_236_25
    have h21 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 27 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 26 1 h20 kg_236_26
    have h22 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 29 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 27 2 h21 kg_236_27
    have h23 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 30 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 29 1 h22 kg_236_29
    have h24 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 31 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 30 1 h23 kg_236_30
    have h25 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 34 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 31 3 h24 kg_236_31
    have h26 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 35 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 34 1 h25 kg_236_34
    have h27 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 36 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 35 1 h26 kg_236_35
    have h28 : IPChk.allR (Pts.glueIB K236.lits KW_236) 0 37 = true := IPChk.allR_join (Pts.glueIB K236.lits KW_236) 0 36 1 h27 kg_236_36
    exact h28
  have hlen : K236.lits.length = 37 := by decide
  intro k h1 h2
  obtain rfl : k = 236 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 236) K236.lits KW_236
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_47 : ∀ k, 237 ≤ k → k < 238 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_237 JW_237 237 1 jr_237
theorem jr6_48 : ∀ k, 238 ≤ k → k < 239 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 10 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 2 = true := kb_238_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 2 1 h0 kb_238_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 3 1 h1 kb_238_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 4 1 h2 kb_238_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 5 1 h3 kb_238_5
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 6 1 h4 kb_238_6
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 7 1 h5 kb_238_7
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K238.lits.getD i 0)) 0 8 2 h6 kb_238_8
    exact h7
  have hg : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 10 = true := by
    have h0 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 2 = true := kg_238_0
    have h1 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 3 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 2 1 h0 kg_238_2
    have h2 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 4 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 3 1 h1 kg_238_3
    have h3 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 5 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 4 1 h2 kg_238_4
    have h4 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 6 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 5 1 h3 kg_238_5
    have h5 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 7 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 6 1 h4 kg_238_6
    have h6 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 8 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 7 1 h5 kg_238_7
    have h7 : IPChk.allR (Pts.glueIB K238.lits KW_238) 0 10 = true := IPChk.allR_join (Pts.glueIB K238.lits KW_238) 0 8 2 h6 kg_238_8
    exact h7
  have hlen : K238.lits.length = 10 := by decide
  intro k h1 h2
  obtain rfl : k = 238 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 238) K238.lits KW_238
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_49 : ∀ k, 239 ≤ k → k < 243 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_239 JW_239 239 4 jr_239
theorem jr6_50 : ∀ k, 243 ≤ k → k < 244 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 20 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 2 = true := kb_243_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 2 2 h0 kb_243_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 4 2 h1 kb_243_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 6 1 h2 kb_243_6
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 7 2 h3 kb_243_7
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 9 1 h4 kb_243_9
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 10 1 h5 kb_243_10
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 11 1 h6 kb_243_11
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 12 1 h7 kb_243_12
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 13 2 h8 kb_243_13
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 15 1 h9 kb_243_15
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 16 1 h10 kb_243_16
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 17 2 h11 kb_243_17
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K243.lits.getD i 0)) 0 19 1 h12 kb_243_19
    exact h13
  have hg : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 20 = true := by
    have h0 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 2 = true := kg_243_0
    have h1 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 4 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 2 2 h0 kg_243_2
    have h2 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 6 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 4 2 h1 kg_243_4
    have h3 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 7 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 6 1 h2 kg_243_6
    have h4 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 9 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 7 2 h3 kg_243_7
    have h5 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 10 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 9 1 h4 kg_243_9
    have h6 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 11 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 10 1 h5 kg_243_10
    have h7 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 12 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 11 1 h6 kg_243_11
    have h8 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 13 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 12 1 h7 kg_243_12
    have h9 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 15 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 13 2 h8 kg_243_13
    have h10 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 16 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 15 1 h9 kg_243_15
    have h11 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 17 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 16 1 h10 kg_243_16
    have h12 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 19 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 17 2 h11 kg_243_17
    have h13 : IPChk.allR (Pts.glueIB K243.lits KW_243) 0 20 = true := IPChk.allR_join (Pts.glueIB K243.lits KW_243) 0 19 1 h12 kg_243_19
    exact h13
  have hlen : K243.lits.length = 20 := by decide
  intro k h1 h2
  obtain rfl : k = 243 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 243) K243.lits KW_243
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_51 : ∀ k, 244 ≤ k → k < 245 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_244 JW_244 244 1 jr_244
theorem jr6_52 : ∀ k, 245 ≤ k → k < 246 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 1 = true := kb_245_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 1 1 h0 kb_245_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K245.lits.getD i 0)) 0 2 1 h1 kb_245_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K245.lits KW_245) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K245.lits KW_245) 0 1 = true := kg_245_0
    have h1 : IPChk.allR (Pts.glueIB K245.lits KW_245) 0 2 = true := IPChk.allR_join (Pts.glueIB K245.lits KW_245) 0 1 1 h0 kg_245_1
    have h2 : IPChk.allR (Pts.glueIB K245.lits KW_245) 0 3 = true := IPChk.allR_join (Pts.glueIB K245.lits KW_245) 0 2 1 h1 kg_245_2
    exact h2
  have hlen : K245.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 245 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 245) K245.lits KW_245
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_53 : ∀ k, 246 ≤ k → k < 247 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_246 JW_246 246 1 jr_246
theorem jr6_54 : ∀ k, 247 ≤ k → k < 248 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 5 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 2 = true := kb_247_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 2 2 h0 kb_247_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K247.lits.getD i 0)) 0 4 1 h1 kb_247_4
    exact h2
  have hg : IPChk.allR (Pts.glueIB K247.lits KW_247) 0 5 = true := by
    have h0 : IPChk.allR (Pts.glueIB K247.lits KW_247) 0 2 = true := kg_247_0
    have h1 : IPChk.allR (Pts.glueIB K247.lits KW_247) 0 4 = true := IPChk.allR_join (Pts.glueIB K247.lits KW_247) 0 2 2 h0 kg_247_2
    have h2 : IPChk.allR (Pts.glueIB K247.lits KW_247) 0 5 = true := IPChk.allR_join (Pts.glueIB K247.lits KW_247) 0 4 1 h1 kg_247_4
    exact h2
  have hlen : K247.lits.length = 5 := by decide
  intro k h1 h2
  obtain rfl : k = 247 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 247) K247.lits KW_247
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_55 : ∀ k, 248 ≤ k → k < 262 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_248 JW_248 248 14 jr_248
theorem jr6_56 : ∀ k, 262 ≤ k → k < 263 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 38 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 3 = true := kb_262_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 3 1 h0 kb_262_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 4 2 h1 kb_262_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 6 1 h2 kb_262_6
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 7 1 h3 kb_262_7
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 8 1 h4 kb_262_8
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 9 1 h5 kb_262_9
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 10 2 h6 kb_262_10
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 12 4 h7 kb_262_12
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 16 1 h8 kb_262_16
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 17 2 h9 kb_262_17
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 19 2 h10 kb_262_19
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 21 1 h11 kb_262_21
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 22 1 h12 kb_262_22
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 23 1 h13 kb_262_23
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 24 1 h14 kb_262_24
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 25 1 h15 kb_262_25
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 26 1 h16 kb_262_26
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 27 2 h17 kb_262_27
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 29 1 h18 kb_262_29
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 30 2 h19 kb_262_30
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 32 2 h20 kb_262_32
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 34 2 h21 kb_262_34
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K262.lits.getD i 0)) 0 36 2 h22 kb_262_36
    exact h23
  have hg : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 38 = true := by
    have h0 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 3 = true := kg_262_0
    have h1 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 4 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 3 1 h0 kg_262_3
    have h2 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 6 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 4 2 h1 kg_262_4
    have h3 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 7 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 6 1 h2 kg_262_6
    have h4 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 8 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 7 1 h3 kg_262_7
    have h5 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 9 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 8 1 h4 kg_262_8
    have h6 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 10 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 9 1 h5 kg_262_9
    have h7 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 12 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 10 2 h6 kg_262_10
    have h8 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 16 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 12 4 h7 kg_262_12
    have h9 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 17 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 16 1 h8 kg_262_16
    have h10 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 19 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 17 2 h9 kg_262_17
    have h11 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 21 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 19 2 h10 kg_262_19
    have h12 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 22 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 21 1 h11 kg_262_21
    have h13 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 23 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 22 1 h12 kg_262_22
    have h14 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 24 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 23 1 h13 kg_262_23
    have h15 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 25 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 24 1 h14 kg_262_24
    have h16 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 26 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 25 1 h15 kg_262_25
    have h17 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 27 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 26 1 h16 kg_262_26
    have h18 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 29 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 27 2 h17 kg_262_27
    have h19 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 30 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 29 1 h18 kg_262_29
    have h20 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 32 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 30 2 h19 kg_262_30
    have h21 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 34 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 32 2 h20 kg_262_32
    have h22 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 36 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 34 2 h21 kg_262_34
    have h23 : IPChk.allR (Pts.glueIB K262.lits KW_262) 0 38 = true := IPChk.allR_join (Pts.glueIB K262.lits KW_262) 0 36 2 h22 kg_262_36
    exact h23
  have hlen : K262.lits.length = 38 := by decide
  intro k h1 h2
  obtain rfl : k = 262 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 262) K262.lits KW_262
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_57 : ∀ k, 263 ≤ k → k < 264 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_263 JW_263 263 1 jr_263
theorem jr6_58 : ∀ k, 264 ≤ k → k < 265 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 1 = true := kb_264_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 1 1 h0 kb_264_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K264.lits.getD i 0)) 0 2 1 h1 kb_264_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K264.lits KW_264) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K264.lits KW_264) 0 1 = true := kg_264_0
    have h1 : IPChk.allR (Pts.glueIB K264.lits KW_264) 0 2 = true := IPChk.allR_join (Pts.glueIB K264.lits KW_264) 0 1 1 h0 kg_264_1
    have h2 : IPChk.allR (Pts.glueIB K264.lits KW_264) 0 3 = true := IPChk.allR_join (Pts.glueIB K264.lits KW_264) 0 2 1 h1 kg_264_2
    exact h2
  have hlen : K264.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 264 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 264) K264.lits KW_264
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_59 : ∀ k, 265 ≤ k → k < 267 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_265 JW_265 265 2 jr_265
theorem jr6_60 : ∀ k, 267 ≤ k → k < 268 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 1 = true := kb_267_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 1 1 h0 kb_267_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K267.lits.getD i 0)) 0 2 1 h1 kb_267_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K267.lits KW_267) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K267.lits KW_267) 0 1 = true := kg_267_0
    have h1 : IPChk.allR (Pts.glueIB K267.lits KW_267) 0 2 = true := IPChk.allR_join (Pts.glueIB K267.lits KW_267) 0 1 1 h0 kg_267_1
    have h2 : IPChk.allR (Pts.glueIB K267.lits KW_267) 0 3 = true := IPChk.allR_join (Pts.glueIB K267.lits KW_267) 0 2 1 h1 kg_267_2
    exact h2
  have hlen : K267.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 267 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 267) K267.lits KW_267
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_61 : ∀ k, 268 ≤ k → k < 270 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_268 JW_268 268 2 jr_268
theorem jr6_62 : ∀ k, 270 ≤ k → k < 273 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_268 JW_268 270 3 jr_270
theorem jr6_63 : ∀ k, 273 ≤ k → k < 287 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_268 JW_268 273 14 jr_273

theorem grp6_1 : ∀ k, 113 ≤ k → k < 287 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_21
  have a1 := Pts.fa_join a0 jr6_22
  have a2 := Pts.fa_join a1 jr6_23
  have a3 := Pts.fa_join a2 jr6_24
  have a4 := Pts.fa_join a3 jr6_25
  have a5 := Pts.fa_join a4 jr6_26
  have a6 := Pts.fa_join a5 jr6_27
  have a7 := Pts.fa_join a6 jr6_28
  have a8 := Pts.fa_join a7 jr6_29
  have a9 := Pts.fa_join a8 jr6_30
  have a10 := Pts.fa_join a9 jr6_31
  have a11 := Pts.fa_join a10 jr6_32
  have a12 := Pts.fa_join a11 jr6_33
  have a13 := Pts.fa_join a12 jr6_34
  have a14 := Pts.fa_join a13 jr6_35
  have a15 := Pts.fa_join a14 jr6_36
  have a16 := Pts.fa_join a15 jr6_37
  have a17 := Pts.fa_join a16 jr6_38
  have a18 := Pts.fa_join a17 jr6_39
  have a19 := Pts.fa_join a18 jr6_40
  have a20 := Pts.fa_join a19 jr6_41
  have a21 := Pts.fa_join a20 jr6_42
  have a22 := Pts.fa_join a21 jr6_43
  have a23 := Pts.fa_join a22 jr6_44
  have a24 := Pts.fa_join a23 jr6_45
  have a25 := Pts.fa_join a24 jr6_46
  have a26 := Pts.fa_join a25 jr6_47
  have a27 := Pts.fa_join a26 jr6_48
  have a28 := Pts.fa_join a27 jr6_49
  have a29 := Pts.fa_join a28 jr6_50
  have a30 := Pts.fa_join a29 jr6_51
  have a31 := Pts.fa_join a30 jr6_52
  have a32 := Pts.fa_join a31 jr6_53
  have a33 := Pts.fa_join a32 jr6_54
  have a34 := Pts.fa_join a33 jr6_55
  have a35 := Pts.fa_join a34 jr6_56
  have a36 := Pts.fa_join a35 jr6_57
  have a37 := Pts.fa_join a36 jr6_58
  have a38 := Pts.fa_join a37 jr6_59
  have a39 := Pts.fa_join a38 jr6_60
  have a40 := Pts.fa_join a39 jr6_61
  have a41 := Pts.fa_join a40 jr6_62
  have a42 := Pts.fa_join a41 jr6_63
  exact a42

end B334.E1x.Pts.S707
