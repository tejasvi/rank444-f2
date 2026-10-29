import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J6897
import B334.E1x.Pts.S707.J6941
import B334.E1x.Pts.S707.J6943
import B334.E1x.Pts.S707.J6973
import B334.E1x.Pts.S707.J6975
import B334.E1x.Pts.S707.J7005
import B334.E1x.Pts.S707.J7046
import B334.E1x.Pts.S707.J7075
import B334.E1x.Pts.S707.J7077
import B334.E1x.Pts.S707.J7083
import B334.E1x.Pts.S707.J7085
import B334.E1x.Pts.S707.J7107
import B334.E1x.Pts.S707.J7155
import B334.E1x.Pts.S707.J7163
import B334.E1x.Pts.S707.J7185
import B334.E1x.Pts.S707.K6893L
import B334.E1x.Pts.S707.K6894L
import B334.E1x.Pts.S707.K6895L
import B334.E1x.Pts.S707.K6896L
import B334.E1x.Pts.S707.K6939L
import B334.E1x.Pts.S707.K6940L
import B334.E1x.Pts.S707.K6942L
import B334.E1x.Pts.S707.K6972L
import B334.E1x.Pts.S707.K6974L
import B334.E1x.Pts.S707.K7004L
import B334.E1x.Pts.S707.K7043L
import B334.E1x.Pts.S707.K7044L
import B334.E1x.Pts.S707.K7045L
import B334.E1x.Pts.S707.K7074L
import B334.E1x.Pts.S707.K7076L
import B334.E1x.Pts.S707.K7082L
import B334.E1x.Pts.S707.K7084L
import B334.E1x.Pts.S707.K7106L
import B334.E1x.Pts.S707.K7154L
import B334.E1x.Pts.S707.K7162L
import B334.E1x.Pts.S707.K7184L
import B334.E1x.Pts.S707.K6893Q0
import B334.E1x.Pts.S707.K6893Q1
import B334.E1x.Pts.S707.K6893Q2
import B334.E1x.Pts.S707.K6894Q0
import B334.E1x.Pts.S707.K6894Q1
import B334.E1x.Pts.S707.K6894Q2
import B334.E1x.Pts.S707.K6894Q3
import B334.E1x.Pts.S707.K6895Q0
import B334.E1x.Pts.S707.K6895Q1
import B334.E1x.Pts.S707.K6896Q0
import B334.E1x.Pts.S707.K6939Q0
import B334.E1x.Pts.S707.K6939Q1
import B334.E1x.Pts.S707.K6939Q2
import B334.E1x.Pts.S707.K6939Q3
import B334.E1x.Pts.S707.K6939Q4
import B334.E1x.Pts.S707.K6939Q5
import B334.E1x.Pts.S707.K6939Q6
import B334.E1x.Pts.S707.K6940Q0
import B334.E1x.Pts.S707.K6940Q1
import B334.E1x.Pts.S707.K6942Q0
import B334.E1x.Pts.S707.K6942Q1
import B334.E1x.Pts.S707.K6942Q2
import B334.E1x.Pts.S707.K6942Q3
import B334.E1x.Pts.S707.K6942Q4
import B334.E1x.Pts.S707.K6942Q5
import B334.E1x.Pts.S707.K6942Q6
import B334.E1x.Pts.S707.K6972Q0
import B334.E1x.Pts.S707.K6972Q1
import B334.E1x.Pts.S707.K6974Q0
import B334.E1x.Pts.S707.K6974Q1
import B334.E1x.Pts.S707.K6974Q2
import B334.E1x.Pts.S707.K6974Q3
import B334.E1x.Pts.S707.K6974Q4
import B334.E1x.Pts.S707.K7004Q0
import B334.E1x.Pts.S707.K7004Q1
import B334.E1x.Pts.S707.K7004Q2
import B334.E1x.Pts.S707.K7004Q3
import B334.E1x.Pts.S707.K7004Q4
import B334.E1x.Pts.S707.K7043Q0
import B334.E1x.Pts.S707.K7043Q1
import B334.E1x.Pts.S707.K7044Q0
import B334.E1x.Pts.S707.K7045Q0
import B334.E1x.Pts.S707.K7074Q0
import B334.E1x.Pts.S707.K7074Q1
import B334.E1x.Pts.S707.K7076Q0
import B334.E1x.Pts.S707.K7082Q0
import B334.E1x.Pts.S707.K7084Q0
import B334.E1x.Pts.S707.K7106Q0
import B334.E1x.Pts.S707.K7154Q0
import B334.E1x.Pts.S707.K7162Q0
import B334.E1x.Pts.S707.K7184Q0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 6893 … 7278 (stage707_v6): the v5 Fin's job blocks r1078 … r1115 as
theorems, joined into `grp6_27` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_1078 : ∀ k, 6893 ≤ k → k < 6894 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 32 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 3 = true := kb_6893_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 3 1 h0 kb_6893_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 4 1 h1 kb_6893_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 5 2 h2 kb_6893_5
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 7 1 h3 kb_6893_7
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 8 1 h4 kb_6893_8
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 9 1 h5 kb_6893_9
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 10 1 h6 kb_6893_10
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 11 1 h7 kb_6893_11
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 12 1 h8 kb_6893_12
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 13 1 h9 kb_6893_13
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 14 1 h10 kb_6893_14
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 15 1 h11 kb_6893_15
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 16 1 h12 kb_6893_16
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 17 1 h13 kb_6893_17
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 18 1 h14 kb_6893_18
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 19 2 h15 kb_6893_19
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 21 2 h16 kb_6893_21
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 23 2 h17 kb_6893_23
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 25 1 h18 kb_6893_25
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 26 1 h19 kb_6893_26
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 27 2 h20 kb_6893_27
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 29 2 h21 kb_6893_29
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6893.lits.getD i 0)) 0 31 1 h22 kb_6893_31
    exact h23
  have hg : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 32 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 3 = true := kg_6893_0
    have h1 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 4 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 3 1 h0 kg_6893_3
    have h2 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 5 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 4 1 h1 kg_6893_4
    have h3 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 7 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 5 2 h2 kg_6893_5
    have h4 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 8 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 7 1 h3 kg_6893_7
    have h5 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 9 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 8 1 h4 kg_6893_8
    have h6 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 10 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 9 1 h5 kg_6893_9
    have h7 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 11 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 10 1 h6 kg_6893_10
    have h8 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 12 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 11 1 h7 kg_6893_11
    have h9 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 13 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 12 1 h8 kg_6893_12
    have h10 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 14 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 13 1 h9 kg_6893_13
    have h11 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 15 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 14 1 h10 kg_6893_14
    have h12 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 16 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 15 1 h11 kg_6893_15
    have h13 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 17 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 16 1 h12 kg_6893_16
    have h14 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 18 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 17 1 h13 kg_6893_17
    have h15 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 19 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 18 1 h14 kg_6893_18
    have h16 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 21 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 19 2 h15 kg_6893_19
    have h17 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 23 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 21 2 h16 kg_6893_21
    have h18 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 25 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 23 2 h17 kg_6893_23
    have h19 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 26 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 25 1 h18 kg_6893_25
    have h20 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 27 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 26 1 h19 kg_6893_26
    have h21 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 29 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 27 2 h20 kg_6893_27
    have h22 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 31 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 29 2 h21 kg_6893_29
    have h23 : IPChk.allR (Pts.glueIB K6893.lits KW_6893) 0 32 = true := IPChk.allR_join (Pts.glueIB K6893.lits KW_6893) 0 31 1 h22 kg_6893_31
    exact h23
  have hlen : K6893.lits.length = 32 := by decide
  intro k h1 h2
  obtain rfl : k = 6893 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6893) K6893.lits KW_6893
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1079 : ∀ k, 6894 ≤ k → k < 6895 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 210 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 2 = true := kb_6894_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 2 1 h0 kb_6894_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 3 9 h1 kb_6894_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 12 1 h2 kb_6894_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 13 1 h3 kb_6894_13
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 14 1 h4 kb_6894_14
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 15 29 h5 kb_6894_15
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 44 2 h6 kb_6894_44
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 46 6 h7 kb_6894_46
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 52 2 h8 kb_6894_52
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 54 55 h9 kb_6894_54
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 109 34 h10 kb_6894_109
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 143 2 h11 kb_6894_143
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 145 1 h12 kb_6894_145
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 146 1 h13 kb_6894_146
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 147 1 h14 kb_6894_147
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 148 2 h15 kb_6894_148
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 150 1 h16 kb_6894_150
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 151 2 h17 kb_6894_151
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 153 2 h18 kb_6894_153
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 155 1 h19 kb_6894_155
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 156 3 h20 kb_6894_156
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 159 3 h21 kb_6894_159
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 162 3 h22 kb_6894_162
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 165 12 h23 kb_6894_165
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 177 1 h24 kb_6894_177
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 178 1 h25 kb_6894_178
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 179 1 h26 kb_6894_179
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 180 1 h27 kb_6894_180
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 181 2 h28 kb_6894_181
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 183 2 h29 kb_6894_183
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 185 1 h30 kb_6894_185
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 186 3 h31 kb_6894_186
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 189 4 h32 kb_6894_189
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 193 9 h33 kb_6894_193
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 202 2 h34 kb_6894_202
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 204 2 h35 kb_6894_204
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6894.lits.getD i 0)) 0 206 4 h36 kb_6894_206
    exact h37
  have hg : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 210 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 2 = true := kg_6894_0
    have h1 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 3 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 2 1 h0 kg_6894_2
    have h2 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 12 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 3 9 h1 kg_6894_3
    have h3 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 13 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 12 1 h2 kg_6894_12
    have h4 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 14 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 13 1 h3 kg_6894_13
    have h5 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 15 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 14 1 h4 kg_6894_14
    have h6 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 44 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 15 29 h5 kg_6894_15
    have h7 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 46 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 44 2 h6 kg_6894_44
    have h8 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 52 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 46 6 h7 kg_6894_46
    have h9 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 54 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 52 2 h8 kg_6894_52
    have h10 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 109 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 54 55 h9 kg_6894_54
    have h11 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 143 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 109 34 h10 kg_6894_109
    have h12 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 145 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 143 2 h11 kg_6894_143
    have h13 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 146 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 145 1 h12 kg_6894_145
    have h14 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 147 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 146 1 h13 kg_6894_146
    have h15 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 148 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 147 1 h14 kg_6894_147
    have h16 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 150 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 148 2 h15 kg_6894_148
    have h17 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 151 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 150 1 h16 kg_6894_150
    have h18 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 153 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 151 2 h17 kg_6894_151
    have h19 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 155 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 153 2 h18 kg_6894_153
    have h20 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 156 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 155 1 h19 kg_6894_155
    have h21 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 159 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 156 3 h20 kg_6894_156
    have h22 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 162 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 159 3 h21 kg_6894_159
    have h23 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 165 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 162 3 h22 kg_6894_162
    have h24 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 177 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 165 12 h23 kg_6894_165
    have h25 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 178 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 177 1 h24 kg_6894_177
    have h26 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 179 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 178 1 h25 kg_6894_178
    have h27 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 180 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 179 1 h26 kg_6894_179
    have h28 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 181 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 180 1 h27 kg_6894_180
    have h29 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 183 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 181 2 h28 kg_6894_181
    have h30 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 185 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 183 2 h29 kg_6894_183
    have h31 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 186 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 185 1 h30 kg_6894_185
    have h32 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 189 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 186 3 h31 kg_6894_186
    have h33 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 193 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 189 4 h32 kg_6894_189
    have h34 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 202 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 193 9 h33 kg_6894_193
    have h35 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 204 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 202 2 h34 kg_6894_202
    have h36 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 206 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 204 2 h35 kg_6894_204
    have h37 : IPChk.allR (Pts.glueIB K6894.lits KW_6894) 0 210 = true := IPChk.allR_join (Pts.glueIB K6894.lits KW_6894) 0 206 4 h36 kg_6894_206
    exact h37
  have hlen : K6894.lits.length = 210 := by decide
  intro k h1 h2
  obtain rfl : k = 6894 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6894) K6894.lits KW_6894
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1080 : ∀ k, 6895 ≤ k → k < 6896 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 163 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 1 = true := kb_6895_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 1 1 h0 kb_6895_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 2 8 h1 kb_6895_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 10 2 h2 kb_6895_10
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 12 29 h3 kb_6895_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 41 2 h4 kb_6895_41
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 43 6 h5 kb_6895_43
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 49 3 h6 kb_6895_49
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 52 79 h7 kb_6895_52
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 131 1 h8 kb_6895_131
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 132 2 h9 kb_6895_132
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 134 4 h10 kb_6895_134
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 138 10 h11 kb_6895_138
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 148 3 h12 kb_6895_148
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 151 1 h13 kb_6895_151
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 152 6 h14 kb_6895_152
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6895.lits.getD i 0)) 0 158 5 h15 kb_6895_158
    exact h16
  have hg : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 163 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 1 = true := kg_6895_0
    have h1 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 2 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 1 1 h0 kg_6895_1
    have h2 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 10 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 2 8 h1 kg_6895_2
    have h3 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 12 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 10 2 h2 kg_6895_10
    have h4 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 41 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 12 29 h3 kg_6895_12
    have h5 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 43 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 41 2 h4 kg_6895_41
    have h6 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 49 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 43 6 h5 kg_6895_43
    have h7 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 52 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 49 3 h6 kg_6895_49
    have h8 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 131 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 52 79 h7 kg_6895_52
    have h9 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 132 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 131 1 h8 kg_6895_131
    have h10 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 134 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 132 2 h9 kg_6895_132
    have h11 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 138 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 134 4 h10 kg_6895_134
    have h12 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 148 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 138 10 h11 kg_6895_138
    have h13 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 151 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 148 3 h12 kg_6895_148
    have h14 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 152 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 151 1 h13 kg_6895_151
    have h15 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 158 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 152 6 h14 kg_6895_152
    have h16 : IPChk.allR (Pts.glueIB K6895.lits KW_6895) 0 163 = true := IPChk.allR_join (Pts.glueIB K6895.lits KW_6895) 0 158 5 h15 kg_6895_158
    exact h16
  have hlen : K6895.lits.length = 163 := by decide
  intro k h1 h2
  obtain rfl : k = 6895 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6895) K6895.lits KW_6895
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1081 : ∀ k, 6896 ≤ k → k < 6897 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 266 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 1 = true := kb_6896_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 1 1 h0 kb_6896_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 2 1 h1 kb_6896_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 3 43 h2 kb_6896_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 46 63 h3 kb_6896_46
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 109 2 h4 kb_6896_109
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 111 53 h5 kb_6896_111
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 264 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 164 100 h6 kb_6896_164
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 266 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6896.lits.getD i 0)) 0 264 2 h7 kb_6896_264
    exact h8
  have hg : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 266 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 1 = true := kg_6896_0
    have h1 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 2 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 1 1 h0 kg_6896_1
    have h2 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 3 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 2 1 h1 kg_6896_2
    have h3 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 46 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 3 43 h2 kg_6896_3
    have h4 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 109 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 46 63 h3 kg_6896_46
    have h5 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 111 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 109 2 h4 kg_6896_109
    have h6 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 164 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 111 53 h5 kg_6896_111
    have h7 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 264 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 164 100 h6 kg_6896_164
    have h8 : IPChk.allR (Pts.glueIB K6896.lits KW_6896) 0 266 = true := IPChk.allR_join (Pts.glueIB K6896.lits KW_6896) 0 264 2 h7 kg_6896_264
    exact h8
  have hlen : K6896.lits.length = 266 := by decide
  intro k h1 h2
  obtain rfl : k = 6896 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6896) K6896.lits KW_6896
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1082 : ∀ k, 6897 ≤ k → k < 6939 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_6897 JW_6897 6897 42 jr_6897
theorem jr6_1083 : ∀ k, 6939 ≤ k → k < 6940 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 358 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 2 = true := kb_6939_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 2 3 h0 kb_6939_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 5 10 h1 kb_6939_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 15 1 h2 kb_6939_15
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 16 1 h3 kb_6939_16
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 17 1 h4 kb_6939_17
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 18 29 h5 kb_6939_18
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 47 2 h6 kb_6939_47
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 49 6 h7 kb_6939_49
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 55 2 h8 kb_6939_55
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 57 22 h9 kb_6939_57
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 79 9 h10 kb_6939_79
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 88 38 h11 kb_6939_88
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 126 6 h12 kb_6939_126
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 132 2 h13 kb_6939_132
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 134 14 h14 kb_6939_134
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 148 1 h15 kb_6939_148
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 149 1 h16 kb_6939_149
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 150 1 h17 kb_6939_150
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 151 1 h18 kb_6939_151
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 152 1 h19 kb_6939_152
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 153 3 h20 kb_6939_153
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 156 6 h21 kb_6939_156
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 162 1 h22 kb_6939_162
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 163 8 h23 kb_6939_163
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 171 2 h24 kb_6939_171
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 173 1 h25 kb_6939_173
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 174 8 h26 kb_6939_174
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 182 1 h27 kb_6939_182
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 183 6 h28 kb_6939_183
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 189 1 h29 kb_6939_189
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 190 9 h30 kb_6939_190
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 199 3 h31 kb_6939_199
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 202 5 h32 kb_6939_202
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 207 1 h33 kb_6939_207
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 208 7 h34 kb_6939_208
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 215 2 h35 kb_6939_215
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 224 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 217 7 h36 kb_6939_217
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 224 2 h37 kb_6939_224
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 226 9 h38 kb_6939_226
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 240 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 235 5 h39 kb_6939_235
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 245 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 240 5 h40 kb_6939_240
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 247 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 245 2 h41 kb_6939_245
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 247 1 h42 kb_6939_247
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 248 1 h43 kb_6939_248
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 249 3 h44 kb_6939_249
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 252 1 h45 kb_6939_252
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 258 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 253 5 h46 kb_6939_253
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 261 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 258 3 h47 kb_6939_258
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 261 2 h48 kb_6939_261
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 268 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 263 5 h49 kb_6939_263
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 268 4 h50 kb_6939_268
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 275 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 272 3 h51 kb_6939_272
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 275 6 h52 kb_6939_275
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 285 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 281 4 h53 kb_6939_281
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 293 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 285 8 h54 kb_6939_285
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 293 5 h55 kb_6939_293
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 298 4 h56 kb_6939_298
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 309 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 302 7 h57 kb_6939_302
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 309 6 h58 kb_6939_309
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 316 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 315 1 h59 kb_6939_315
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 316 3 h60 kb_6939_316
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 319 2 h61 kb_6939_319
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 327 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 321 6 h62 kb_6939_321
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 327 3 h63 kb_6939_327
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 330 2 h64 kb_6939_330
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 335 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 332 3 h65 kb_6939_332
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 335 3 h66 kb_6939_335
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 338 3 h67 kb_6939_338
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 341 3 h68 kb_6939_341
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 344 4 h69 kb_6939_344
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 348 5 h70 kb_6939_348
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 353 4 h71 kb_6939_353
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6939.lits.getD i 0)) 0 357 1 h72 kb_6939_357
    exact h73
  have hg : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 358 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 2 = true := kg_6939_0
    have h1 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 5 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 2 3 h0 kg_6939_2
    have h2 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 15 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 5 10 h1 kg_6939_5
    have h3 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 16 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 15 1 h2 kg_6939_15
    have h4 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 17 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 16 1 h3 kg_6939_16
    have h5 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 18 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 17 1 h4 kg_6939_17
    have h6 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 47 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 18 29 h5 kg_6939_18
    have h7 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 49 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 47 2 h6 kg_6939_47
    have h8 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 55 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 49 6 h7 kg_6939_49
    have h9 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 57 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 55 2 h8 kg_6939_55
    have h10 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 79 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 57 22 h9 kg_6939_57
    have h11 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 88 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 79 9 h10 kg_6939_79
    have h12 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 126 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 88 38 h11 kg_6939_88
    have h13 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 132 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 126 6 h12 kg_6939_126
    have h14 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 134 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 132 2 h13 kg_6939_132
    have h15 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 148 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 134 14 h14 kg_6939_134
    have h16 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 149 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 148 1 h15 kg_6939_148
    have h17 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 150 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 149 1 h16 kg_6939_149
    have h18 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 151 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 150 1 h17 kg_6939_150
    have h19 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 152 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 151 1 h18 kg_6939_151
    have h20 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 153 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 152 1 h19 kg_6939_152
    have h21 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 156 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 153 3 h20 kg_6939_153
    have h22 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 162 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 156 6 h21 kg_6939_156
    have h23 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 163 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 162 1 h22 kg_6939_162
    have h24 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 171 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 163 8 h23 kg_6939_163
    have h25 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 173 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 171 2 h24 kg_6939_171
    have h26 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 174 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 173 1 h25 kg_6939_173
    have h27 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 182 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 174 8 h26 kg_6939_174
    have h28 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 183 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 182 1 h27 kg_6939_182
    have h29 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 189 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 183 6 h28 kg_6939_183
    have h30 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 190 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 189 1 h29 kg_6939_189
    have h31 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 199 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 190 9 h30 kg_6939_190
    have h32 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 202 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 199 3 h31 kg_6939_199
    have h33 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 207 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 202 5 h32 kg_6939_202
    have h34 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 208 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 207 1 h33 kg_6939_207
    have h35 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 215 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 208 7 h34 kg_6939_208
    have h36 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 217 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 215 2 h35 kg_6939_215
    have h37 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 224 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 217 7 h36 kg_6939_217
    have h38 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 226 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 224 2 h37 kg_6939_224
    have h39 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 235 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 226 9 h38 kg_6939_226
    have h40 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 240 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 235 5 h39 kg_6939_235
    have h41 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 245 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 240 5 h40 kg_6939_240
    have h42 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 247 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 245 2 h41 kg_6939_245
    have h43 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 248 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 247 1 h42 kg_6939_247
    have h44 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 249 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 248 1 h43 kg_6939_248
    have h45 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 252 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 249 3 h44 kg_6939_249
    have h46 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 253 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 252 1 h45 kg_6939_252
    have h47 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 258 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 253 5 h46 kg_6939_253
    have h48 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 261 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 258 3 h47 kg_6939_258
    have h49 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 263 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 261 2 h48 kg_6939_261
    have h50 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 268 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 263 5 h49 kg_6939_263
    have h51 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 272 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 268 4 h50 kg_6939_268
    have h52 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 275 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 272 3 h51 kg_6939_272
    have h53 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 281 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 275 6 h52 kg_6939_275
    have h54 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 285 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 281 4 h53 kg_6939_281
    have h55 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 293 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 285 8 h54 kg_6939_285
    have h56 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 298 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 293 5 h55 kg_6939_293
    have h57 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 302 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 298 4 h56 kg_6939_298
    have h58 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 309 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 302 7 h57 kg_6939_302
    have h59 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 315 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 309 6 h58 kg_6939_309
    have h60 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 316 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 315 1 h59 kg_6939_315
    have h61 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 319 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 316 3 h60 kg_6939_316
    have h62 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 321 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 319 2 h61 kg_6939_319
    have h63 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 327 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 321 6 h62 kg_6939_321
    have h64 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 330 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 327 3 h63 kg_6939_327
    have h65 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 332 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 330 2 h64 kg_6939_330
    have h66 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 335 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 332 3 h65 kg_6939_332
    have h67 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 338 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 335 3 h66 kg_6939_335
    have h68 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 341 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 338 3 h67 kg_6939_338
    have h69 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 344 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 341 3 h68 kg_6939_341
    have h70 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 348 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 344 4 h69 kg_6939_344
    have h71 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 353 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 348 5 h70 kg_6939_348
    have h72 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 357 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 353 4 h71 kg_6939_353
    have h73 : IPChk.allR (Pts.glueIB K6939.lits KW_6939) 0 358 = true := IPChk.allR_join (Pts.glueIB K6939.lits KW_6939) 0 357 1 h72 kg_6939_357
    exact h73
  have hlen : K6939.lits.length = 358 := by decide
  intro k h1 h2
  obtain rfl : k = 6939 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6939) K6939.lits KW_6939
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1084 : ∀ k, 6940 ≤ k → k < 6941 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 161 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 1 = true := kb_6940_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 1 1 h0 kb_6940_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 2 5 h1 kb_6940_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 7 1 h2 kb_6940_7
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 8 12 h3 kb_6940_8
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 20 104 h4 kb_6940_20
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 124 4 h5 kb_6940_124
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 128 5 h6 kb_6940_128
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 133 1 h7 kb_6940_133
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 134 4 h8 kb_6940_134
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 138 1 h9 kb_6940_138
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 139 4 h10 kb_6940_139
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 143 1 h11 kb_6940_143
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 144 1 h12 kb_6940_144
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 145 3 h13 kb_6940_145
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 148 2 h14 kb_6940_148
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 150 3 h15 kb_6940_150
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 153 2 h16 kb_6940_153
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 155 5 h17 kb_6940_155
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6940.lits.getD i 0)) 0 160 1 h18 kb_6940_160
    exact h19
  have hg : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 161 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 1 = true := kg_6940_0
    have h1 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 2 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 1 1 h0 kg_6940_1
    have h2 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 7 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 2 5 h1 kg_6940_2
    have h3 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 8 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 7 1 h2 kg_6940_7
    have h4 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 20 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 8 12 h3 kg_6940_8
    have h5 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 124 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 20 104 h4 kg_6940_20
    have h6 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 128 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 124 4 h5 kg_6940_124
    have h7 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 133 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 128 5 h6 kg_6940_128
    have h8 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 134 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 133 1 h7 kg_6940_133
    have h9 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 138 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 134 4 h8 kg_6940_134
    have h10 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 139 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 138 1 h9 kg_6940_138
    have h11 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 143 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 139 4 h10 kg_6940_139
    have h12 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 144 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 143 1 h11 kg_6940_143
    have h13 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 145 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 144 1 h12 kg_6940_144
    have h14 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 148 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 145 3 h13 kg_6940_145
    have h15 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 150 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 148 2 h14 kg_6940_148
    have h16 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 153 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 150 3 h15 kg_6940_150
    have h17 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 155 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 153 2 h16 kg_6940_153
    have h18 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 160 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 155 5 h17 kg_6940_155
    have h19 : IPChk.allR (Pts.glueIB K6940.lits KW_6940) 0 161 = true := IPChk.allR_join (Pts.glueIB K6940.lits KW_6940) 0 160 1 h18 kg_6940_160
    exact h19
  have hlen : K6940.lits.length = 161 := by decide
  intro k h1 h2
  obtain rfl : k = 6940 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6940) K6940.lits KW_6940
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1085 : ∀ k, 6941 ≤ k → k < 6942 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_6941 JW_6941 6941 1 jr_6941
theorem jr6_1086 : ∀ k, 6942 ≤ k → k < 6943 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 672 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 1 = true := kb_6942_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 1 1 h0 kb_6942_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 2 2 h1 kb_6942_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 4 28 h2 kb_6942_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 32 2 h3 kb_6942_32
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 34 6 h4 kb_6942_34
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 40 2 h5 kb_6942_40
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 42 16 h6 kb_6942_42
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 58 9 h7 kb_6942_58
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 74 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 67 7 h8 kb_6942_67
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 74 38 h9 kb_6942_74
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 112 2 h10 kb_6942_112
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 114 4 h11 kb_6942_114
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 118 10 h12 kb_6942_118
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 128 8 h13 kb_6942_128
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 136 2 h14 kb_6942_136
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 138 12 h15 kb_6942_138
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 150 7 h16 kb_6942_150
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 157 2 h17 kb_6942_157
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 159 12 h18 kb_6942_159
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 171 3 h19 kb_6942_171
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 174 6 h20 kb_6942_174
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 180 2 h21 kb_6942_180
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 182 20 h22 kb_6942_182
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 202 3 h23 kb_6942_202
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 205 6 h24 kb_6942_205
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 211 20 h25 kb_6942_211
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 234 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 231 3 h26 kb_6942_231
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 252 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 234 18 h27 kb_6942_234
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 253 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 252 1 h28 kb_6942_252
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 265 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 253 12 h29 kb_6942_253
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 265 9 h30 kb_6942_265
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 274 2 h31 kb_6942_274
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 276 29 h32 kb_6942_276
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 305 2 h33 kb_6942_305
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 307 6 h34 kb_6942_307
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 315 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 313 2 h35 kb_6942_313
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 315 22 h36 kb_6942_315
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 337 16 h37 kb_6942_337
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 353 35 h38 kb_6942_353
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 388 4 h39 kb_6942_388
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 392 15 h40 kb_6942_392
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 411 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 407 4 h41 kb_6942_407
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 425 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 411 14 h42 kb_6942_411
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 428 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 425 3 h43 kb_6942_425
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 428 10 h44 kb_6942_428
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 438 12 h45 kb_6942_438
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 450 18 h46 kb_6942_450
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 468 4 h47 kb_6942_468
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 472 7 h48 kb_6942_472
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 493 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 479 14 h49 kb_6942_479
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 493 15 h50 kb_6942_493
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 508 6 h51 kb_6942_508
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 514 2 h52 kb_6942_514
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 528 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 516 12 h53 kb_6942_516
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 550 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 528 22 h54 kb_6942_528
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 553 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 550 3 h55 kb_6942_550
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 565 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 553 12 h56 kb_6942_553
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 565 1 h57 kb_6942_565
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 573 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 566 7 h58 kb_6942_566
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 584 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 573 11 h59 kb_6942_573
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 590 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 584 6 h60 kb_6942_584
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 590 7 h61 kb_6942_590
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 597 12 h62 kb_6942_597
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 645 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 609 36 h63 kb_6942_609
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 657 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 645 12 h64 kb_6942_645
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6942.lits.getD i 0)) 0 657 15 h65 kb_6942_657
    exact h66
  have hg : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 672 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 1 = true := kg_6942_0
    have h1 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 2 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 1 1 h0 kg_6942_1
    have h2 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 4 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 2 2 h1 kg_6942_2
    have h3 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 32 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 4 28 h2 kg_6942_4
    have h4 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 34 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 32 2 h3 kg_6942_32
    have h5 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 40 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 34 6 h4 kg_6942_34
    have h6 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 42 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 40 2 h5 kg_6942_40
    have h7 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 58 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 42 16 h6 kg_6942_42
    have h8 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 67 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 58 9 h7 kg_6942_58
    have h9 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 74 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 67 7 h8 kg_6942_67
    have h10 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 112 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 74 38 h9 kg_6942_74
    have h11 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 114 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 112 2 h10 kg_6942_112
    have h12 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 118 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 114 4 h11 kg_6942_114
    have h13 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 128 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 118 10 h12 kg_6942_118
    have h14 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 136 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 128 8 h13 kg_6942_128
    have h15 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 138 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 136 2 h14 kg_6942_136
    have h16 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 150 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 138 12 h15 kg_6942_138
    have h17 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 157 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 150 7 h16 kg_6942_150
    have h18 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 159 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 157 2 h17 kg_6942_157
    have h19 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 171 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 159 12 h18 kg_6942_159
    have h20 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 174 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 171 3 h19 kg_6942_171
    have h21 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 180 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 174 6 h20 kg_6942_174
    have h22 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 182 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 180 2 h21 kg_6942_180
    have h23 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 202 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 182 20 h22 kg_6942_182
    have h24 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 205 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 202 3 h23 kg_6942_202
    have h25 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 211 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 205 6 h24 kg_6942_205
    have h26 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 231 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 211 20 h25 kg_6942_211
    have h27 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 234 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 231 3 h26 kg_6942_231
    have h28 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 252 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 234 18 h27 kg_6942_234
    have h29 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 253 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 252 1 h28 kg_6942_252
    have h30 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 265 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 253 12 h29 kg_6942_253
    have h31 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 274 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 265 9 h30 kg_6942_265
    have h32 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 276 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 274 2 h31 kg_6942_274
    have h33 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 305 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 276 29 h32 kg_6942_276
    have h34 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 307 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 305 2 h33 kg_6942_305
    have h35 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 313 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 307 6 h34 kg_6942_307
    have h36 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 315 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 313 2 h35 kg_6942_313
    have h37 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 337 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 315 22 h36 kg_6942_315
    have h38 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 353 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 337 16 h37 kg_6942_337
    have h39 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 388 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 353 35 h38 kg_6942_353
    have h40 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 392 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 388 4 h39 kg_6942_388
    have h41 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 407 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 392 15 h40 kg_6942_392
    have h42 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 411 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 407 4 h41 kg_6942_407
    have h43 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 425 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 411 14 h42 kg_6942_411
    have h44 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 428 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 425 3 h43 kg_6942_425
    have h45 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 438 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 428 10 h44 kg_6942_428
    have h46 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 450 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 438 12 h45 kg_6942_438
    have h47 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 468 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 450 18 h46 kg_6942_450
    have h48 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 472 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 468 4 h47 kg_6942_468
    have h49 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 479 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 472 7 h48 kg_6942_472
    have h50 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 493 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 479 14 h49 kg_6942_479
    have h51 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 508 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 493 15 h50 kg_6942_493
    have h52 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 514 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 508 6 h51 kg_6942_508
    have h53 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 516 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 514 2 h52 kg_6942_514
    have h54 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 528 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 516 12 h53 kg_6942_516
    have h55 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 550 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 528 22 h54 kg_6942_528
    have h56 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 553 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 550 3 h55 kg_6942_550
    have h57 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 565 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 553 12 h56 kg_6942_553
    have h58 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 566 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 565 1 h57 kg_6942_565
    have h59 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 573 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 566 7 h58 kg_6942_566
    have h60 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 584 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 573 11 h59 kg_6942_573
    have h61 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 590 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 584 6 h60 kg_6942_584
    have h62 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 597 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 590 7 h61 kg_6942_590
    have h63 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 609 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 597 12 h62 kg_6942_597
    have h64 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 645 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 609 36 h63 kg_6942_609
    have h65 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 657 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 645 12 h64 kg_6942_645
    have h66 : IPChk.allR (Pts.glueIB K6942.lits KW_6942) 0 672 = true := IPChk.allR_join (Pts.glueIB K6942.lits KW_6942) 0 657 15 h65 kg_6942_657
    exact h66
  have hlen : K6942.lits.length = 672 := by decide
  intro k h1 h2
  obtain rfl : k = 6942 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6942) K6942.lits KW_6942
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1087 : ∀ k, 6943 ≤ k → k < 6972 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_6943 JW_6943 6943 29 jr_6943
theorem jr6_1088 : ∀ k, 6972 ≤ k → k < 6973 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 35 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 6 = true := kb_6972_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 6 2 h0 kb_6972_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 8 9 h1 kb_6972_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 17 1 h2 kb_6972_17
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 18 1 h3 kb_6972_18
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 19 1 h4 kb_6972_19
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 20 1 h5 kb_6972_20
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 21 3 h6 kb_6972_21
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 24 3 h7 kb_6972_24
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 27 1 h8 kb_6972_27
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 28 1 h9 kb_6972_28
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 29 2 h10 kb_6972_29
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 31 1 h11 kb_6972_31
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 32 1 h12 kb_6972_32
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6972.lits.getD i 0)) 0 33 2 h13 kb_6972_33
    exact h14
  have hg : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 35 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 6 = true := kg_6972_0
    have h1 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 8 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 6 2 h0 kg_6972_6
    have h2 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 17 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 8 9 h1 kg_6972_8
    have h3 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 18 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 17 1 h2 kg_6972_17
    have h4 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 19 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 18 1 h3 kg_6972_18
    have h5 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 20 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 19 1 h4 kg_6972_19
    have h6 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 21 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 20 1 h5 kg_6972_20
    have h7 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 24 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 21 3 h6 kg_6972_21
    have h8 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 27 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 24 3 h7 kg_6972_24
    have h9 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 28 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 27 1 h8 kg_6972_27
    have h10 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 29 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 28 1 h9 kg_6972_28
    have h11 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 31 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 29 2 h10 kg_6972_29
    have h12 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 32 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 31 1 h11 kg_6972_31
    have h13 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 33 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 32 1 h12 kg_6972_32
    have h14 : IPChk.allR (Pts.glueIB K6972.lits KW_6972) 0 35 = true := IPChk.allR_join (Pts.glueIB K6972.lits KW_6972) 0 33 2 h13 kg_6972_33
    exact h14
  have hlen : K6972.lits.length = 35 := by decide
  intro k h1 h2
  obtain rfl : k = 6972 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6972) K6972.lits KW_6972
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1089 : ∀ k, 6973 ≤ k → k < 6974 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_6973 JW_6973 6973 1 jr_6973
theorem jr6_1090 : ∀ k, 6974 ≤ k → k < 6975 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 476 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 1 = true := kb_6974_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 1 2 h0 kb_6974_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 3 21 h1 kb_6974_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 24 2 h2 kb_6974_24
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 26 6 h3 kb_6974_26
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 32 2 h4 kb_6974_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 34 16 h5 kb_6974_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 50 4 h6 kb_6974_50
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 54 1 h7 kb_6974_54
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 55 5 h8 kb_6974_55
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 76 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 60 16 h9 kb_6974_60
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 76 2 h10 kb_6974_76
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 78 20 h11 kb_6974_78
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 98 2 h12 kb_6974_98
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 100 15 h13 kb_6974_100
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 115 6 h14 kb_6974_115
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 121 2 h15 kb_6974_121
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 123 23 h16 kb_6974_123
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 146 2 h17 kb_6974_146
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 148 19 h18 kb_6974_148
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 167 2 h19 kb_6974_167
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 169 15 h20 kb_6974_169
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 184 17 h21 kb_6974_184
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 201 1 h22 kb_6974_201
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 202 29 h23 kb_6974_202
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 233 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 231 2 h24 kb_6974_231
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 233 6 h25 kb_6974_233
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 239 2 h26 kb_6974_239
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 241 64 h27 kb_6974_241
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 305 17 h28 kb_6974_305
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 323 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 322 1 h29 kb_6974_322
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 323 11 h30 kb_6974_323
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 334 9 h31 kb_6974_334
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 343 12 h32 kb_6974_343
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 355 18 h33 kb_6974_355
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 373 5 h34 kb_6974_373
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 386 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 378 8 h35 kb_6974_378
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 399 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 386 13 h36 kb_6974_386
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 399 5 h37 kb_6974_399
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 404 1 h38 kb_6974_404
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 405 5 h39 kb_6974_405
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 410 17 h40 kb_6974_410
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 430 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 427 3 h41 kb_6974_427
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 430 7 h42 kb_6974_430
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 437 12 h43 kb_6974_437
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 449 4 h44 kb_6974_449
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 465 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 453 12 h45 kb_6974_453
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 476 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6974.lits.getD i 0)) 0 465 11 h46 kb_6974_465
    exact h47
  have hg : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 476 = true := by
    have h0 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 1 = true := kg_6974_0
    have h1 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 3 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 1 2 h0 kg_6974_1
    have h2 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 24 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 3 21 h1 kg_6974_3
    have h3 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 26 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 24 2 h2 kg_6974_24
    have h4 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 32 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 26 6 h3 kg_6974_26
    have h5 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 34 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 32 2 h4 kg_6974_32
    have h6 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 50 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 34 16 h5 kg_6974_34
    have h7 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 54 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 50 4 h6 kg_6974_50
    have h8 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 55 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 54 1 h7 kg_6974_54
    have h9 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 60 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 55 5 h8 kg_6974_55
    have h10 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 76 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 60 16 h9 kg_6974_60
    have h11 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 78 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 76 2 h10 kg_6974_76
    have h12 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 98 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 78 20 h11 kg_6974_78
    have h13 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 100 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 98 2 h12 kg_6974_98
    have h14 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 115 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 100 15 h13 kg_6974_100
    have h15 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 121 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 115 6 h14 kg_6974_115
    have h16 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 123 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 121 2 h15 kg_6974_121
    have h17 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 146 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 123 23 h16 kg_6974_123
    have h18 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 148 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 146 2 h17 kg_6974_146
    have h19 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 167 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 148 19 h18 kg_6974_148
    have h20 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 169 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 167 2 h19 kg_6974_167
    have h21 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 184 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 169 15 h20 kg_6974_169
    have h22 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 201 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 184 17 h21 kg_6974_184
    have h23 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 202 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 201 1 h22 kg_6974_201
    have h24 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 231 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 202 29 h23 kg_6974_202
    have h25 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 233 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 231 2 h24 kg_6974_231
    have h26 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 239 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 233 6 h25 kg_6974_233
    have h27 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 241 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 239 2 h26 kg_6974_239
    have h28 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 305 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 241 64 h27 kg_6974_241
    have h29 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 322 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 305 17 h28 kg_6974_305
    have h30 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 323 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 322 1 h29 kg_6974_322
    have h31 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 334 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 323 11 h30 kg_6974_323
    have h32 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 343 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 334 9 h31 kg_6974_334
    have h33 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 355 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 343 12 h32 kg_6974_343
    have h34 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 373 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 355 18 h33 kg_6974_355
    have h35 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 378 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 373 5 h34 kg_6974_373
    have h36 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 386 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 378 8 h35 kg_6974_378
    have h37 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 399 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 386 13 h36 kg_6974_386
    have h38 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 404 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 399 5 h37 kg_6974_399
    have h39 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 405 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 404 1 h38 kg_6974_404
    have h40 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 410 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 405 5 h39 kg_6974_405
    have h41 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 427 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 410 17 h40 kg_6974_410
    have h42 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 430 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 427 3 h41 kg_6974_427
    have h43 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 437 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 430 7 h42 kg_6974_430
    have h44 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 449 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 437 12 h43 kg_6974_437
    have h45 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 453 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 449 4 h44 kg_6974_449
    have h46 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 465 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 453 12 h45 kg_6974_453
    have h47 : IPChk.allR (Pts.glueIB K6974.lits KW_6974) 0 476 = true := IPChk.allR_join (Pts.glueIB K6974.lits KW_6974) 0 465 11 h46 kg_6974_465
    exact h47
  have hlen : K6974.lits.length = 476 := by decide
  intro k h1 h2
  obtain rfl : k = 6974 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 6974) K6974.lits KW_6974
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1091 : ∀ k, 6975 ≤ k → k < 7004 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_6975 JW_6975 6975 29 jr_6975
theorem jr6_1092 : ∀ k, 7004 ≤ k → k < 7005 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 492 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 1 = true := kb_7004_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 1 1 h0 kb_7004_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 2 1 h1 kb_7004_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 3 20 h2 kb_7004_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 23 2 h3 kb_7004_23
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 25 6 h4 kb_7004_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 31 2 h5 kb_7004_31
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 33 20 h6 kb_7004_33
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 53 3 h7 kb_7004_53
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 56 2 h8 kb_7004_56
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 58 4 h9 kb_7004_58
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 62 13 h10 kb_7004_62
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 75 2 h11 kb_7004_75
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 95 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 77 18 h12 kb_7004_77
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 95 3 h13 kb_7004_95
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 98 13 h14 kb_7004_98
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 111 2 h15 kb_7004_111
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 113 6 h16 kb_7004_113
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 119 1 h17 kb_7004_119
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 120 17 h18 kb_7004_120
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 137 7 h19 kb_7004_137
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 144 2 h20 kb_7004_144
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 146 15 h21 kb_7004_146
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 161 13 h22 kb_7004_161
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 174 15 h23 kb_7004_174
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 189 1 h24 kb_7004_189
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 212 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 190 22 h25 kb_7004_190
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 212 9 h26 kb_7004_212
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 221 6 h27 kb_7004_221
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 227 5 h28 kb_7004_227
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 297 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 232 65 h29 kb_7004_232
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 301 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 297 4 h30 kb_7004_297
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 302 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 301 1 h31 kb_7004_301
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 332 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 302 30 h32 kb_7004_302
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 358 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 332 26 h33 kb_7004_332
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 363 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 358 5 h34 kb_7004_358
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 363 17 h35 kb_7004_363
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 380 18 h36 kb_7004_380
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 398 22 h37 kb_7004_398
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 429 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 420 9 h38 kb_7004_420
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 429 20 h39 kb_7004_429
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 449 11 h40 kb_7004_449
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 460 12 h41 kb_7004_460
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7004.lits.getD i 0)) 0 472 20 h42 kb_7004_472
    exact h43
  have hg : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 492 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 1 = true := kg_7004_0
    have h1 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 2 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 1 1 h0 kg_7004_1
    have h2 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 3 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 2 1 h1 kg_7004_2
    have h3 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 23 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 3 20 h2 kg_7004_3
    have h4 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 25 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 23 2 h3 kg_7004_23
    have h5 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 31 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 25 6 h4 kg_7004_25
    have h6 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 33 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 31 2 h5 kg_7004_31
    have h7 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 53 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 33 20 h6 kg_7004_33
    have h8 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 56 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 53 3 h7 kg_7004_53
    have h9 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 58 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 56 2 h8 kg_7004_56
    have h10 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 62 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 58 4 h9 kg_7004_58
    have h11 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 75 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 62 13 h10 kg_7004_62
    have h12 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 77 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 75 2 h11 kg_7004_75
    have h13 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 95 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 77 18 h12 kg_7004_77
    have h14 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 98 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 95 3 h13 kg_7004_95
    have h15 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 111 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 98 13 h14 kg_7004_98
    have h16 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 113 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 111 2 h15 kg_7004_111
    have h17 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 119 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 113 6 h16 kg_7004_113
    have h18 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 120 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 119 1 h17 kg_7004_119
    have h19 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 137 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 120 17 h18 kg_7004_120
    have h20 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 144 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 137 7 h19 kg_7004_137
    have h21 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 146 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 144 2 h20 kg_7004_144
    have h22 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 161 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 146 15 h21 kg_7004_146
    have h23 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 174 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 161 13 h22 kg_7004_161
    have h24 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 189 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 174 15 h23 kg_7004_174
    have h25 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 190 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 189 1 h24 kg_7004_189
    have h26 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 212 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 190 22 h25 kg_7004_190
    have h27 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 221 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 212 9 h26 kg_7004_212
    have h28 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 227 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 221 6 h27 kg_7004_221
    have h29 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 232 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 227 5 h28 kg_7004_227
    have h30 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 297 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 232 65 h29 kg_7004_232
    have h31 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 301 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 297 4 h30 kg_7004_297
    have h32 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 302 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 301 1 h31 kg_7004_301
    have h33 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 332 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 302 30 h32 kg_7004_302
    have h34 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 358 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 332 26 h33 kg_7004_332
    have h35 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 363 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 358 5 h34 kg_7004_358
    have h36 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 380 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 363 17 h35 kg_7004_363
    have h37 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 398 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 380 18 h36 kg_7004_380
    have h38 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 420 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 398 22 h37 kg_7004_398
    have h39 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 429 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 420 9 h38 kg_7004_420
    have h40 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 449 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 429 20 h39 kg_7004_429
    have h41 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 460 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 449 11 h40 kg_7004_449
    have h42 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 472 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 460 12 h41 kg_7004_460
    have h43 : IPChk.allR (Pts.glueIB K7004.lits KW_7004) 0 492 = true := IPChk.allR_join (Pts.glueIB K7004.lits KW_7004) 0 472 20 h42 kg_7004_472
    exact h43
  have hlen : K7004.lits.length = 492 := by decide
  intro k h1 h2
  obtain rfl : k = 7004 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7004) K7004.lits KW_7004
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1093 : ∀ k, 7005 ≤ k → k < 7043 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7005 JW_7005 7005 38 jr_7005
theorem jr6_1094 : ∀ k, 7043 ≤ k → k < 7044 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 213 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 1 = true := kb_7043_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 1 6 h0 kb_7043_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 7 4 h1 kb_7043_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 11 11 h2 kb_7043_11
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 22 1 h3 kb_7043_22
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 23 9 h4 kb_7043_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 32 2 h5 kb_7043_32
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 34 6 h6 kb_7043_34
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 40 2 h7 kb_7043_40
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 42 19 h8 kb_7043_42
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 61 2 h9 kb_7043_61
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 63 4 h10 kb_7043_63
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 67 2 h11 kb_7043_67
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 69 20 h12 kb_7043_69
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 89 21 h13 kb_7043_89
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 110 14 h14 kb_7043_110
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 124 14 h15 kb_7043_124
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 138 12 h16 kb_7043_138
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 150 53 h17 kb_7043_150
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7043.lits.getD i 0)) 0 203 10 h18 kb_7043_203
    exact h19
  have hg : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 213 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 1 = true := kg_7043_0
    have h1 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 7 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 1 6 h0 kg_7043_1
    have h2 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 11 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 7 4 h1 kg_7043_7
    have h3 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 22 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 11 11 h2 kg_7043_11
    have h4 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 23 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 22 1 h3 kg_7043_22
    have h5 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 32 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 23 9 h4 kg_7043_23
    have h6 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 34 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 32 2 h5 kg_7043_32
    have h7 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 40 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 34 6 h6 kg_7043_34
    have h8 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 42 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 40 2 h7 kg_7043_40
    have h9 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 61 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 42 19 h8 kg_7043_42
    have h10 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 63 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 61 2 h9 kg_7043_61
    have h11 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 67 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 63 4 h10 kg_7043_63
    have h12 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 69 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 67 2 h11 kg_7043_67
    have h13 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 89 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 69 20 h12 kg_7043_69
    have h14 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 110 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 89 21 h13 kg_7043_89
    have h15 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 124 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 110 14 h14 kg_7043_110
    have h16 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 138 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 124 14 h15 kg_7043_124
    have h17 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 150 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 138 12 h16 kg_7043_138
    have h18 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 203 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 150 53 h17 kg_7043_150
    have h19 : IPChk.allR (Pts.glueIB K7043.lits KW_7043) 0 213 = true := IPChk.allR_join (Pts.glueIB K7043.lits KW_7043) 0 203 10 h18 kg_7043_203
    exact h19
  have hlen : K7043.lits.length = 213 := by decide
  intro k h1 h2
  obtain rfl : k = 7043 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7043) K7043.lits KW_7043
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1095 : ∀ k, 7044 ≤ k → k < 7045 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 94 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 11 = true := kb_7044_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 11 2 h0 kb_7044_11
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 13 13 h1 kb_7044_13
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 26 10 h2 kb_7044_26
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 36 24 h3 kb_7044_36
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7044.lits.getD i 0)) 0 60 34 h4 kb_7044_60
    exact h5
  have hg : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 94 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 11 = true := kg_7044_0
    have h1 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 13 = true := IPChk.allR_join (Pts.glueIB K7044.lits KW_7044) 0 11 2 h0 kg_7044_11
    have h2 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 26 = true := IPChk.allR_join (Pts.glueIB K7044.lits KW_7044) 0 13 13 h1 kg_7044_13
    have h3 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 36 = true := IPChk.allR_join (Pts.glueIB K7044.lits KW_7044) 0 26 10 h2 kg_7044_26
    have h4 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 60 = true := IPChk.allR_join (Pts.glueIB K7044.lits KW_7044) 0 36 24 h3 kg_7044_36
    have h5 : IPChk.allR (Pts.glueIB K7044.lits KW_7044) 0 94 = true := IPChk.allR_join (Pts.glueIB K7044.lits KW_7044) 0 60 34 h4 kg_7044_60
    exact h5
  have hlen : K7044.lits.length = 94 := by decide
  intro k h1 h2
  obtain rfl : k = 7044 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7044) K7044.lits KW_7044
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1096 : ∀ k, 7045 ≤ k → k < 7046 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 99 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 11 = true := kb_7045_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 11 2 h0 kb_7045_11
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 13 14 h1 kb_7045_13
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 27 5 h2 kb_7045_27
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 32 17 h3 kb_7045_32
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 49 31 h4 kb_7045_49
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7045.lits.getD i 0)) 0 80 19 h5 kb_7045_80
    exact h6
  have hg : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 99 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 11 = true := kg_7045_0
    have h1 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 13 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 11 2 h0 kg_7045_11
    have h2 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 27 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 13 14 h1 kg_7045_13
    have h3 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 32 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 27 5 h2 kg_7045_27
    have h4 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 49 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 32 17 h3 kg_7045_32
    have h5 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 80 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 49 31 h4 kg_7045_49
    have h6 : IPChk.allR (Pts.glueIB K7045.lits KW_7045) 0 99 = true := IPChk.allR_join (Pts.glueIB K7045.lits KW_7045) 0 80 19 h5 kg_7045_80
    exact h6
  have hlen : K7045.lits.length = 99 := by decide
  intro k h1 h2
  obtain rfl : k = 7045 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7045) K7045.lits KW_7045
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1097 : ∀ k, 7046 ≤ k → k < 7074 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7046 JW_7046 7046 28 jr_7046
theorem jr6_1098 : ∀ k, 7074 ≤ k → k < 7075 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 110 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 2 = true := kb_7074_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 2 6 h0 kb_7074_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 8 2 h1 kb_7074_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 10 21 h2 kb_7074_10
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 31 1 h3 kb_7074_31
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 32 2 h4 kb_7074_32
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 34 5 h5 kb_7074_34
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 39 2 h6 kb_7074_39
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 41 15 h7 kb_7074_41
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 56 30 h8 kb_7074_56
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 91 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 86 5 h9 kb_7074_86
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 91 18 h10 kb_7074_91
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7074.lits.getD i 0)) 0 109 1 h11 kb_7074_109
    exact h12
  have hg : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 110 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 2 = true := kg_7074_0
    have h1 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 8 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 2 6 h0 kg_7074_2
    have h2 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 10 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 8 2 h1 kg_7074_8
    have h3 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 31 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 10 21 h2 kg_7074_10
    have h4 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 32 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 31 1 h3 kg_7074_31
    have h5 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 34 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 32 2 h4 kg_7074_32
    have h6 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 39 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 34 5 h5 kg_7074_34
    have h7 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 41 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 39 2 h6 kg_7074_39
    have h8 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 56 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 41 15 h7 kg_7074_41
    have h9 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 86 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 56 30 h8 kg_7074_56
    have h10 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 91 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 86 5 h9 kg_7074_86
    have h11 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 109 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 91 18 h10 kg_7074_91
    have h12 : IPChk.allR (Pts.glueIB K7074.lits KW_7074) 0 110 = true := IPChk.allR_join (Pts.glueIB K7074.lits KW_7074) 0 109 1 h11 kg_7074_109
    exact h12
  have hlen : K7074.lits.length = 110 := by decide
  intro k h1 h2
  obtain rfl : k = 7074 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7074) K7074.lits KW_7074
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1099 : ∀ k, 7075 ≤ k → k < 7076 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7075 JW_7075 7075 1 jr_7075
theorem jr6_1100 : ∀ k, 7076 ≤ k → k < 7077 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 72 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 6 = true := kb_7076_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 6 2 h0 kb_7076_6
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 8 20 h1 kb_7076_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 28 2 h2 kb_7076_28
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 30 19 h3 kb_7076_30
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 49 1 h4 kb_7076_49
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 50 8 h5 kb_7076_50
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7076.lits.getD i 0)) 0 58 14 h6 kb_7076_58
    exact h7
  have hg : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 72 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 6 = true := kg_7076_0
    have h1 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 8 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 6 2 h0 kg_7076_6
    have h2 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 28 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 8 20 h1 kg_7076_8
    have h3 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 30 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 28 2 h2 kg_7076_28
    have h4 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 49 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 30 19 h3 kg_7076_30
    have h5 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 50 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 49 1 h4 kg_7076_49
    have h6 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 58 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 50 8 h5 kg_7076_50
    have h7 : IPChk.allR (Pts.glueIB K7076.lits KW_7076) 0 72 = true := IPChk.allR_join (Pts.glueIB K7076.lits KW_7076) 0 58 14 h6 kg_7076_58
    exact h7
  have hlen : K7076.lits.length = 72 := by decide
  intro k h1 h2
  obtain rfl : k = 7076 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7076) K7076.lits KW_7076
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1101 : ∀ k, 7077 ≤ k → k < 7082 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7077 JW_7077 7077 5 jr_7077
theorem jr6_1102 : ∀ k, 7082 ≤ k → k < 7083 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 40 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 2 = true := kb_7082_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 2 18 h0 kb_7082_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 20 4 h1 kb_7082_20
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 24 9 h2 kb_7082_24
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7082.lits.getD i 0)) 0 33 7 h3 kb_7082_33
    exact h4
  have hg : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 40 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 2 = true := kg_7082_0
    have h1 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 20 = true := IPChk.allR_join (Pts.glueIB K7082.lits KW_7082) 0 2 18 h0 kg_7082_2
    have h2 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 24 = true := IPChk.allR_join (Pts.glueIB K7082.lits KW_7082) 0 20 4 h1 kg_7082_20
    have h3 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 33 = true := IPChk.allR_join (Pts.glueIB K7082.lits KW_7082) 0 24 9 h2 kg_7082_24
    have h4 : IPChk.allR (Pts.glueIB K7082.lits KW_7082) 0 40 = true := IPChk.allR_join (Pts.glueIB K7082.lits KW_7082) 0 33 7 h3 kg_7082_33
    exact h4
  have hlen : K7082.lits.length = 40 := by decide
  intro k h1 h2
  obtain rfl : k = 7082 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7082) K7082.lits KW_7082
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1103 : ∀ k, 7083 ≤ k → k < 7084 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7083 JW_7083 7083 1 jr_7083
theorem jr6_1104 : ∀ k, 7084 ≤ k → k < 7085 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 24 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 15 = true := kb_7084_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 15 8 h0 kb_7084_15
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 23 1 h1 kb_7084_23
    exact h2
  have hg : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 0 24 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 0 15 = true := kg_7084_0
    have h1 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 0 23 = true := IPChk.allR_join (Pts.glueIB K7084.lits KW_7084) 0 15 8 h0 kg_7084_15
    have h2 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 0 24 = true := IPChk.allR_join (Pts.glueIB K7084.lits KW_7084) 0 23 1 h1 kg_7084_23
    exact h2
  have hlen : K7084.lits.length = 24 := by decide
  intro k h1 h2
  obtain rfl : k = 7084 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7084) K7084.lits KW_7084
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1105 : ∀ k, 7085 ≤ k → k < 7106 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7085 JW_7085 7085 21 jr_7085
theorem jr6_1106 : ∀ k, 7106 ≤ k → k < 7107 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 0 2 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 0 1 = true := kb_7106_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7106.lits.getD i 0)) 0 1 1 h0 kb_7106_1
    exact h1
  have hg : IPChk.allR (Pts.glueIB K7106.lits KW_7106) 0 2 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7106.lits KW_7106) 0 1 = true := kg_7106_0
    have h1 : IPChk.allR (Pts.glueIB K7106.lits KW_7106) 0 2 = true := IPChk.allR_join (Pts.glueIB K7106.lits KW_7106) 0 1 1 h0 kg_7106_1
    exact h1
  have hlen : K7106.lits.length = 2 := by decide
  intro k h1 h2
  obtain rfl : k = 7106 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7106) K7106.lits KW_7106
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1107 : ∀ k, 7107 ≤ k → k < 7116 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7107 JW_7107 7107 9 jr_7107
theorem jr6_1108 : ∀ k, 7116 ≤ k → k < 7154 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7107 JW_7107 7116 38 jr_7116
theorem jr6_1109 : ∀ k, 7154 ≤ k → k < 7155 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7154.lits.getD i 0)) 0 25 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7154.lits.getD i 0)) 0 3 = true := kb_7154_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7154.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7154.lits.getD i 0)) 0 3 22 h0 kb_7154_3
    exact h1
  have hg : IPChk.allR (Pts.glueIB K7154.lits KW_7154) 0 25 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7154.lits KW_7154) 0 3 = true := kg_7154_0
    have h1 : IPChk.allR (Pts.glueIB K7154.lits KW_7154) 0 25 = true := IPChk.allR_join (Pts.glueIB K7154.lits KW_7154) 0 3 22 h0 kg_7154_3
    exact h1
  have hlen : K7154.lits.length = 25 := by decide
  intro k h1 h2
  obtain rfl : k = 7154 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7154) K7154.lits KW_7154
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1110 : ∀ k, 7155 ≤ k → k < 7162 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7155 JW_7155 7155 7 jr_7155
theorem jr6_1111 : ∀ k, 7162 ≤ k → k < 7163 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 12 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 9 = true := kb_7162_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 9 2 h0 kb_7162_9
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7162.lits.getD i 0)) 0 11 1 h1 kb_7162_11
    exact h2
  have hg : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 0 12 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 0 9 = true := kg_7162_0
    have h1 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 0 11 = true := IPChk.allR_join (Pts.glueIB K7162.lits KW_7162) 0 9 2 h0 kg_7162_9
    have h2 : IPChk.allR (Pts.glueIB K7162.lits KW_7162) 0 12 = true := IPChk.allR_join (Pts.glueIB K7162.lits KW_7162) 0 11 1 h1 kg_7162_11
    exact h2
  have hlen : K7162.lits.length = 12 := by decide
  intro k h1 h2
  obtain rfl : k = 7162 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7162) K7162.lits KW_7162
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1112 : ∀ k, 7163 ≤ k → k < 7184 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7163 JW_7163 7163 21 jr_7163
theorem jr6_1113 : ∀ k, 7184 ≤ k → k < 7185 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 4 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 1 = true := kb_7184_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 1 2 h0 kb_7184_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7184.lits.getD i 0)) 0 3 1 h1 kb_7184_3
    exact h2
  have hg : IPChk.allR (Pts.glueIB K7184.lits KW_7184) 0 4 = true := by
    have h0 : IPChk.allR (Pts.glueIB K7184.lits KW_7184) 0 1 = true := kg_7184_0
    have h1 : IPChk.allR (Pts.glueIB K7184.lits KW_7184) 0 3 = true := IPChk.allR_join (Pts.glueIB K7184.lits KW_7184) 0 1 2 h0 kg_7184_1
    have h2 : IPChk.allR (Pts.glueIB K7184.lits KW_7184) 0 4 = true := IPChk.allR_join (Pts.glueIB K7184.lits KW_7184) 0 3 1 h1 kg_7184_3
    exact h2
  have hlen : K7184.lits.length = 4 := by decide
  intro k h1 h2
  obtain rfl : k = 7184 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 7184) K7184.lits KW_7184
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_1114 : ∀ k, 7185 ≤ k → k < 7235 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7185 JW_7185 7185 50 jr_7185
theorem jr6_1115 : ∀ k, 7235 ≤ k → k < 7279 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_7185 JW_7185 7235 44 jr_7235

theorem grp6_27 : ∀ k, 6893 ≤ k → k < 7279 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_1078
  have a1 := Pts.fa_join a0 jr6_1079
  have a2 := Pts.fa_join a1 jr6_1080
  have a3 := Pts.fa_join a2 jr6_1081
  have a4 := Pts.fa_join a3 jr6_1082
  have a5 := Pts.fa_join a4 jr6_1083
  have a6 := Pts.fa_join a5 jr6_1084
  have a7 := Pts.fa_join a6 jr6_1085
  have a8 := Pts.fa_join a7 jr6_1086
  have a9 := Pts.fa_join a8 jr6_1087
  have a10 := Pts.fa_join a9 jr6_1088
  have a11 := Pts.fa_join a10 jr6_1089
  have a12 := Pts.fa_join a11 jr6_1090
  have a13 := Pts.fa_join a12 jr6_1091
  have a14 := Pts.fa_join a13 jr6_1092
  have a15 := Pts.fa_join a14 jr6_1093
  have a16 := Pts.fa_join a15 jr6_1094
  have a17 := Pts.fa_join a16 jr6_1095
  have a18 := Pts.fa_join a17 jr6_1096
  have a19 := Pts.fa_join a18 jr6_1097
  have a20 := Pts.fa_join a19 jr6_1098
  have a21 := Pts.fa_join a20 jr6_1099
  have a22 := Pts.fa_join a21 jr6_1100
  have a23 := Pts.fa_join a22 jr6_1101
  have a24 := Pts.fa_join a23 jr6_1102
  have a25 := Pts.fa_join a24 jr6_1103
  have a26 := Pts.fa_join a25 jr6_1104
  have a27 := Pts.fa_join a26 jr6_1105
  have a28 := Pts.fa_join a27 jr6_1106
  have a29 := Pts.fa_join a28 jr6_1107
  have a30 := Pts.fa_join a29 jr6_1108
  have a31 := Pts.fa_join a30 jr6_1109
  have a32 := Pts.fa_join a31 jr6_1110
  have a33 := Pts.fa_join a32 jr6_1111
  have a34 := Pts.fa_join a33 jr6_1112
  have a35 := Pts.fa_join a34 jr6_1113
  have a36 := Pts.fa_join a35 jr6_1114
  have a37 := Pts.fa_join a36 jr6_1115
  exact a37

end B334.E1x.Pts.S707
