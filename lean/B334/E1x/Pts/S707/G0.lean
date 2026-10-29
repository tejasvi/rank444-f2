import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J0
import B334.E1x.Pts.S707.J11
import B334.E1x.Pts.S707.J14
import B334.E1x.Pts.S707.J17
import B334.E1x.Pts.S707.J19
import B334.E1x.Pts.S707.J44
import B334.E1x.Pts.S707.J92
import B334.E1x.Pts.S707.J95
import B334.E1x.Pts.S707.J97
import B334.E1x.Pts.S707.K8L
import B334.E1x.Pts.S707.K9L
import B334.E1x.Pts.S707.K10L
import B334.E1x.Pts.S707.K12L
import B334.E1x.Pts.S707.K13L
import B334.E1x.Pts.S707.K16L
import B334.E1x.Pts.S707.K18L
import B334.E1x.Pts.S707.K43L
import B334.E1x.Pts.S707.K8C0
import B334.E1x.Pts.S707.K91L
import B334.E1x.Pts.S707.K94L
import B334.E1x.Pts.S707.K96L
import B334.E1x.Pts.S707.K9C0
import B334.E1x.Pts.S707.K9C1
import B334.E1x.Pts.S707.K10C0
import B334.E1x.Pts.S707.K10C1
import B334.E1x.Pts.S707.K10C2
import B334.E1x.Pts.S707.K10C3
import B334.E1x.Pts.S707.K10C4
import B334.E1x.Pts.S707.K10C5
import B334.E1x.Pts.S707.K12C0
import B334.E1x.Pts.S707.K13C0
import B334.E1x.Pts.S707.K13C1
import B334.E1x.Pts.S707.K13C2
import B334.E1x.Pts.S707.K16C0
import B334.E1x.Pts.S707.K16C1
import B334.E1x.Pts.S707.K16C2
import B334.E1x.Pts.S707.K18C0
import B334.E1x.Pts.S707.K43C0
import B334.E1x.Pts.S707.K91Q0
import B334.E1x.Pts.S707.K91Q1
import B334.E1x.Pts.S707.K91Q2
import B334.E1x.Pts.S707.K91Q3
import B334.E1x.Pts.S707.K91Q4
import B334.E1x.Pts.S707.K91Q5
import B334.E1x.Pts.S707.K91Q6
import B334.E1x.Pts.S707.K91Q7
import B334.E1x.Pts.S707.K91Q8
import B334.E1x.Pts.S707.K91Q9
import B334.E1x.Pts.S707.K94C0
import B334.E1x.Pts.S707.K94C1
import B334.E1x.Pts.S707.K96C0
import B334.E1x.Pts.S707.K91Q10
import B334.E1x.Pts.S707.K91Q11
import B334.E1x.Pts.S707.K91Q12
import B334.E1x.Pts.S707.K91Q13
import B334.E1x.Pts.S707.K91Q14
import B334.E1x.Pts.S707.K91Q15
import B334.E1x.Pts.S707.K91Q16
import B334.E1x.Pts.S707.K91Q17
import B334.E1x.Pts.S707.K91Q18
import B334.E1x.Pts.S707.K91Q19
import B334.E1x.Pts.S707.K91Q20
import B334.E1x.Pts.S707.K91Q21
import B334.E1x.Pts.S707.K91Q22
import B334.E1x.Pts.S707.K91Q23
import B334.E1x.Pts.S707.K91Q24
import B334.E1x.Pts.S707.K91Q25
import B334.E1x.Pts.S707.K91Q26
import B334.E1x.Pts.S707.K91Q27
import B334.E1x.Pts.S707.K91Q28
import B334.E1x.Pts.S707.K91Q29
import B334.E1x.Pts.S707.K91Q30
import B334.E1x.Pts.S707.K91Q31
import B334.E1x.Pts.S707.K91Q32
import B334.E1x.Pts.S707.K91Q33
import B334.E1x.Pts.S707.K91Q34
import B334.E1x.Pts.S707.K91Q35
import B334.E1x.Pts.S707.K91Q36

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 0 … 112 (stage707_v6): the v5 Fin's job blocks r0 … r20 as
theorems, joined into `grp6_0` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_0 : ∀ k, 0 ≤ k → k < 8 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_0 JW_0 0 8 jr_0
theorem jr6_1 : ∀ k, 8 ≤ k → k < 9 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 18 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 1 = true := kb_8_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 1 1 h0 kb_8_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 2 1 h1 kb_8_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 3 1 h2 kb_8_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 4 1 h3 kb_8_4
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 5 1 h4 kb_8_5
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 6 1 h5 kb_8_6
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 7 1 h6 kb_8_7
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 8 2 h7 kb_8_8
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 10 2 h8 kb_8_10
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 12 2 h9 kb_8_12
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 14 1 h10 kb_8_14
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 15 2 h11 kb_8_15
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K8.lits.getD i 0)) 0 17 1 h12 kb_8_17
    exact h13
  have hg : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 18 = true := by
    have h0 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 1 = true := kg_8_0
    have h1 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 2 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 1 1 h0 kg_8_1
    have h2 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 3 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 2 1 h1 kg_8_2
    have h3 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 4 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 3 1 h2 kg_8_3
    have h4 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 5 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 4 1 h3 kg_8_4
    have h5 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 6 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 5 1 h4 kg_8_5
    have h6 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 7 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 6 1 h5 kg_8_6
    have h7 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 8 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 7 1 h6 kg_8_7
    have h8 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 10 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 8 2 h7 kg_8_8
    have h9 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 12 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 10 2 h8 kg_8_10
    have h10 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 14 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 12 2 h9 kg_8_12
    have h11 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 15 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 14 1 h10 kg_8_14
    have h12 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 17 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 15 2 h11 kg_8_15
    have h13 : IPChk.allR (Pts.glueIB K8.lits KW_8) 0 18 = true := IPChk.allR_join (Pts.glueIB K8.lits KW_8) 0 17 1 h12 kg_8_17
    exact h13
  have hlen : K8.lits.length = 18 := by decide
  intro k h1 h2
  obtain rfl : k = 8 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 8) K8.lits KW_8
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_2 : ∀ k, 9 ≤ k → k < 10 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 43 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 1 = true := kb_9_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 1 1 h0 kb_9_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 2 2 h1 kb_9_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 4 1 h2 kb_9_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 5 2 h3 kb_9_5
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 7 1 h4 kb_9_7
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 8 2 h5 kb_9_8
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 10 1 h6 kb_9_10
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 11 1 h7 kb_9_11
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 12 2 h8 kb_9_12
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 14 1 h9 kb_9_14
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 15 1 h10 kb_9_15
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 16 1 h11 kb_9_16
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 17 2 h12 kb_9_17
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 19 3 h13 kb_9_19
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 22 2 h14 kb_9_22
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 24 3 h15 kb_9_24
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 27 3 h16 kb_9_27
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 31 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 30 1 h17 kb_9_30
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 31 2 h18 kb_9_31
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 33 2 h19 kb_9_33
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 35 2 h20 kb_9_35
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 37 1 h21 kb_9_37
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 38 1 h22 kb_9_38
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 39 2 h23 kb_9_39
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K9.lits.getD i 0)) 0 41 2 h24 kb_9_41
    exact h25
  have hg : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 43 = true := by
    have h0 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 1 = true := kg_9_0
    have h1 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 2 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 1 1 h0 kg_9_1
    have h2 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 4 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 2 2 h1 kg_9_2
    have h3 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 5 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 4 1 h2 kg_9_4
    have h4 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 7 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 5 2 h3 kg_9_5
    have h5 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 8 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 7 1 h4 kg_9_7
    have h6 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 10 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 8 2 h5 kg_9_8
    have h7 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 11 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 10 1 h6 kg_9_10
    have h8 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 12 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 11 1 h7 kg_9_11
    have h9 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 14 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 12 2 h8 kg_9_12
    have h10 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 15 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 14 1 h9 kg_9_14
    have h11 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 16 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 15 1 h10 kg_9_15
    have h12 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 17 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 16 1 h11 kg_9_16
    have h13 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 19 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 17 2 h12 kg_9_17
    have h14 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 22 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 19 3 h13 kg_9_19
    have h15 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 24 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 22 2 h14 kg_9_22
    have h16 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 27 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 24 3 h15 kg_9_24
    have h17 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 30 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 27 3 h16 kg_9_27
    have h18 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 31 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 30 1 h17 kg_9_30
    have h19 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 33 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 31 2 h18 kg_9_31
    have h20 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 35 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 33 2 h19 kg_9_33
    have h21 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 37 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 35 2 h20 kg_9_35
    have h22 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 38 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 37 1 h21 kg_9_37
    have h23 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 39 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 38 1 h22 kg_9_38
    have h24 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 41 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 39 2 h23 kg_9_39
    have h25 : IPChk.allR (Pts.glueIB K9.lits KW_9) 0 43 = true := IPChk.allR_join (Pts.glueIB K9.lits KW_9) 0 41 2 h24 kg_9_41
    exact h25
  have hlen : K9.lits.length = 43 := by decide
  intro k h1 h2
  obtain rfl : k = 9 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 9) K9.lits KW_9
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_3 : ∀ k, 10 ≤ k → k < 11 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 190 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 2 = true := kb_10_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 2 1 h0 kb_10_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 3 1 h1 kb_10_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 4 1 h2 kb_10_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 5 1 h3 kb_10_5
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 6 1 h4 kb_10_6
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 7 2 h5 kb_10_7
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 9 2 h6 kb_10_9
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 11 1 h7 kb_10_11
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 12 1 h8 kb_10_12
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 13 1 h9 kb_10_13
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 14 2 h10 kb_10_14
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 16 1 h11 kb_10_16
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 17 1 h12 kb_10_17
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 18 1 h13 kb_10_18
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 19 2 h14 kb_10_19
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 21 1 h15 kb_10_21
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 22 1 h16 kb_10_22
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 23 1 h17 kb_10_23
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 24 2 h18 kb_10_24
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 27 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 26 1 h19 kb_10_26
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 27 1 h20 kb_10_27
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 28 2 h21 kb_10_28
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 30 2 h22 kb_10_30
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 32 2 h23 kb_10_32
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 34 1 h24 kb_10_34
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 35 2 h25 kb_10_35
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 37 2 h26 kb_10_37
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 39 2 h27 kb_10_39
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 41 1 h28 kb_10_41
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 42 2 h29 kb_10_42
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 44 1 h30 kb_10_44
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 45 3 h31 kb_10_45
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 48 1 h32 kb_10_48
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 49 1 h33 kb_10_49
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 50 2 h34 kb_10_50
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 52 1 h35 kb_10_52
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 53 1 h36 kb_10_53
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 54 2 h37 kb_10_54
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 56 3 h38 kb_10_56
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 59 2 h39 kb_10_59
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 61 1 h40 kb_10_61
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 62 1 h41 kb_10_62
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 63 3 h42 kb_10_63
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 66 2 h43 kb_10_66
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 68 1 h44 kb_10_68
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 69 1 h45 kb_10_69
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 70 2 h46 kb_10_70
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 72 1 h47 kb_10_72
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 73 2 h48 kb_10_73
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 75 2 h49 kb_10_75
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 78 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 77 1 h50 kb_10_77
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 78 1 h51 kb_10_78
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 79 1 h52 kb_10_79
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 80 1 h53 kb_10_80
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 81 2 h54 kb_10_81
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 85 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 83 2 h55 kb_10_83
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 85 3 h56 kb_10_85
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 88 2 h57 kb_10_88
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 90 2 h58 kb_10_90
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 94 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 92 2 h59 kb_10_92
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 94 2 h60 kb_10_94
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 97 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 96 1 h61 kb_10_96
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 98 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 97 1 h62 kb_10_97
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 98 1 h63 kb_10_98
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 99 1 h64 kb_10_99
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 100 1 h65 kb_10_100
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 101 1 h66 kb_10_101
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 102 1 h67 kb_10_102
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 103 1 h68 kb_10_103
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 104 2 h69 kb_10_104
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 106 1 h70 kb_10_106
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 107 2 h71 kb_10_107
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 109 2 h72 kb_10_109
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 111 1 h73 kb_10_111
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 112 2 h74 kb_10_112
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 114 2 h75 kb_10_114
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 116 2 h76 kb_10_116
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 118 1 h77 kb_10_118
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 119 2 h78 kb_10_119
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 121 2 h79 kb_10_121
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 123 2 h80 kb_10_123
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 125 2 h81 kb_10_125
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 127 1 h82 kb_10_127
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 128 2 h83 kb_10_128
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 130 2 h84 kb_10_130
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 132 1 h85 kb_10_132
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 133 2 h86 kb_10_133
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 135 2 h87 kb_10_135
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 137 2 h88 kb_10_137
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 139 1 h89 kb_10_139
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 140 1 h90 kb_10_140
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 141 1 h91 kb_10_141
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 142 1 h92 kb_10_142
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 143 1 h93 kb_10_143
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 146 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 144 2 h94 kb_10_144
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 146 1 h95 kb_10_146
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 147 1 h96 kb_10_147
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 149 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 148 1 h97 kb_10_148
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 149 1 h98 kb_10_149
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 150 2 h99 kb_10_150
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 152 2 h100 kb_10_152
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 154 1 h101 kb_10_154
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 155 1 h102 kb_10_155
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 156 1 h103 kb_10_156
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 157 1 h104 kb_10_157
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 158 3 h105 kb_10_158
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 161 2 h106 kb_10_161
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 163 1 h107 kb_10_163
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 164 1 h108 kb_10_164
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 165 1 h109 kb_10_165
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 166 1 h110 kb_10_166
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 167 2 h111 kb_10_167
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 169 2 h112 kb_10_169
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 171 1 h113 kb_10_171
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 172 1 h114 kb_10_172
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 173 1 h115 kb_10_173
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 174 1 h116 kb_10_174
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 175 1 h117 kb_10_175
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 176 1 h118 kb_10_176
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 177 1 h119 kb_10_177
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 178 2 h120 kb_10_178
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 180 2 h121 kb_10_180
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 182 2 h122 kb_10_182
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 184 1 h123 kb_10_184
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 185 1 h124 kb_10_185
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 186 2 h125 kb_10_186
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 188 1 h126 kb_10_188
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K10.lits.getD i 0)) 0 189 1 h127 kb_10_189
    exact h128
  have hg : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 190 = true := by
    have h0 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 2 = true := kg_10_0
    have h1 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 3 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 2 1 h0 kg_10_2
    have h2 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 4 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 3 1 h1 kg_10_3
    have h3 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 5 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 4 1 h2 kg_10_4
    have h4 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 6 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 5 1 h3 kg_10_5
    have h5 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 7 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 6 1 h4 kg_10_6
    have h6 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 9 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 7 2 h5 kg_10_7
    have h7 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 11 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 9 2 h6 kg_10_9
    have h8 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 12 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 11 1 h7 kg_10_11
    have h9 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 13 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 12 1 h8 kg_10_12
    have h10 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 14 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 13 1 h9 kg_10_13
    have h11 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 16 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 14 2 h10 kg_10_14
    have h12 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 17 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 16 1 h11 kg_10_16
    have h13 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 18 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 17 1 h12 kg_10_17
    have h14 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 19 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 18 1 h13 kg_10_18
    have h15 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 21 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 19 2 h14 kg_10_19
    have h16 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 22 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 21 1 h15 kg_10_21
    have h17 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 23 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 22 1 h16 kg_10_22
    have h18 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 24 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 23 1 h17 kg_10_23
    have h19 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 26 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 24 2 h18 kg_10_24
    have h20 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 27 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 26 1 h19 kg_10_26
    have h21 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 28 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 27 1 h20 kg_10_27
    have h22 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 30 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 28 2 h21 kg_10_28
    have h23 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 32 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 30 2 h22 kg_10_30
    have h24 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 34 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 32 2 h23 kg_10_32
    have h25 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 35 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 34 1 h24 kg_10_34
    have h26 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 37 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 35 2 h25 kg_10_35
    have h27 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 39 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 37 2 h26 kg_10_37
    have h28 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 41 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 39 2 h27 kg_10_39
    have h29 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 42 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 41 1 h28 kg_10_41
    have h30 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 44 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 42 2 h29 kg_10_42
    have h31 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 45 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 44 1 h30 kg_10_44
    have h32 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 48 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 45 3 h31 kg_10_45
    have h33 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 49 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 48 1 h32 kg_10_48
    have h34 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 50 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 49 1 h33 kg_10_49
    have h35 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 52 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 50 2 h34 kg_10_50
    have h36 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 53 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 52 1 h35 kg_10_52
    have h37 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 54 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 53 1 h36 kg_10_53
    have h38 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 56 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 54 2 h37 kg_10_54
    have h39 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 59 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 56 3 h38 kg_10_56
    have h40 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 61 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 59 2 h39 kg_10_59
    have h41 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 62 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 61 1 h40 kg_10_61
    have h42 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 63 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 62 1 h41 kg_10_62
    have h43 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 66 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 63 3 h42 kg_10_63
    have h44 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 68 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 66 2 h43 kg_10_66
    have h45 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 69 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 68 1 h44 kg_10_68
    have h46 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 70 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 69 1 h45 kg_10_69
    have h47 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 72 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 70 2 h46 kg_10_70
    have h48 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 73 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 72 1 h47 kg_10_72
    have h49 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 75 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 73 2 h48 kg_10_73
    have h50 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 77 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 75 2 h49 kg_10_75
    have h51 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 78 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 77 1 h50 kg_10_77
    have h52 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 79 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 78 1 h51 kg_10_78
    have h53 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 80 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 79 1 h52 kg_10_79
    have h54 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 81 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 80 1 h53 kg_10_80
    have h55 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 83 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 81 2 h54 kg_10_81
    have h56 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 85 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 83 2 h55 kg_10_83
    have h57 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 88 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 85 3 h56 kg_10_85
    have h58 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 90 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 88 2 h57 kg_10_88
    have h59 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 92 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 90 2 h58 kg_10_90
    have h60 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 94 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 92 2 h59 kg_10_92
    have h61 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 96 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 94 2 h60 kg_10_94
    have h62 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 97 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 96 1 h61 kg_10_96
    have h63 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 98 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 97 1 h62 kg_10_97
    have h64 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 99 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 98 1 h63 kg_10_98
    have h65 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 100 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 99 1 h64 kg_10_99
    have h66 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 101 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 100 1 h65 kg_10_100
    have h67 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 102 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 101 1 h66 kg_10_101
    have h68 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 103 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 102 1 h67 kg_10_102
    have h69 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 104 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 103 1 h68 kg_10_103
    have h70 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 106 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 104 2 h69 kg_10_104
    have h71 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 107 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 106 1 h70 kg_10_106
    have h72 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 109 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 107 2 h71 kg_10_107
    have h73 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 111 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 109 2 h72 kg_10_109
    have h74 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 112 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 111 1 h73 kg_10_111
    have h75 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 114 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 112 2 h74 kg_10_112
    have h76 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 116 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 114 2 h75 kg_10_114
    have h77 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 118 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 116 2 h76 kg_10_116
    have h78 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 119 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 118 1 h77 kg_10_118
    have h79 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 121 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 119 2 h78 kg_10_119
    have h80 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 123 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 121 2 h79 kg_10_121
    have h81 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 125 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 123 2 h80 kg_10_123
    have h82 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 127 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 125 2 h81 kg_10_125
    have h83 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 128 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 127 1 h82 kg_10_127
    have h84 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 130 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 128 2 h83 kg_10_128
    have h85 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 132 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 130 2 h84 kg_10_130
    have h86 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 133 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 132 1 h85 kg_10_132
    have h87 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 135 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 133 2 h86 kg_10_133
    have h88 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 137 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 135 2 h87 kg_10_135
    have h89 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 139 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 137 2 h88 kg_10_137
    have h90 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 140 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 139 1 h89 kg_10_139
    have h91 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 141 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 140 1 h90 kg_10_140
    have h92 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 142 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 141 1 h91 kg_10_141
    have h93 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 143 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 142 1 h92 kg_10_142
    have h94 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 144 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 143 1 h93 kg_10_143
    have h95 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 146 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 144 2 h94 kg_10_144
    have h96 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 147 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 146 1 h95 kg_10_146
    have h97 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 148 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 147 1 h96 kg_10_147
    have h98 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 149 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 148 1 h97 kg_10_148
    have h99 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 150 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 149 1 h98 kg_10_149
    have h100 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 152 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 150 2 h99 kg_10_150
    have h101 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 154 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 152 2 h100 kg_10_152
    have h102 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 155 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 154 1 h101 kg_10_154
    have h103 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 156 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 155 1 h102 kg_10_155
    have h104 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 157 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 156 1 h103 kg_10_156
    have h105 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 158 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 157 1 h104 kg_10_157
    have h106 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 161 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 158 3 h105 kg_10_158
    have h107 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 163 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 161 2 h106 kg_10_161
    have h108 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 164 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 163 1 h107 kg_10_163
    have h109 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 165 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 164 1 h108 kg_10_164
    have h110 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 166 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 165 1 h109 kg_10_165
    have h111 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 167 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 166 1 h110 kg_10_166
    have h112 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 169 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 167 2 h111 kg_10_167
    have h113 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 171 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 169 2 h112 kg_10_169
    have h114 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 172 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 171 1 h113 kg_10_171
    have h115 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 173 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 172 1 h114 kg_10_172
    have h116 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 174 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 173 1 h115 kg_10_173
    have h117 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 175 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 174 1 h116 kg_10_174
    have h118 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 176 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 175 1 h117 kg_10_175
    have h119 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 177 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 176 1 h118 kg_10_176
    have h120 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 178 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 177 1 h119 kg_10_177
    have h121 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 180 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 178 2 h120 kg_10_178
    have h122 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 182 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 180 2 h121 kg_10_180
    have h123 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 184 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 182 2 h122 kg_10_182
    have h124 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 185 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 184 1 h123 kg_10_184
    have h125 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 186 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 185 1 h124 kg_10_185
    have h126 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 188 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 186 2 h125 kg_10_186
    have h127 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 189 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 188 1 h126 kg_10_188
    have h128 : IPChk.allR (Pts.glueIB K10.lits KW_10) 0 190 = true := IPChk.allR_join (Pts.glueIB K10.lits KW_10) 0 189 1 h127 kg_10_189
    exact h128
  have hlen : K10.lits.length = 190 := by decide
  intro k h1 h2
  obtain rfl : k = 10 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 10) K10.lits KW_10
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_4 : ∀ k, 11 ≤ k → k < 12 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_11 JW_11 11 1 jr_11
theorem jr6_5 : ∀ k, 12 ≤ k → k < 13 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 3 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 1 = true := kb_12_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 1 1 h0 kb_12_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K12.lits.getD i 0)) 0 2 1 h1 kb_12_2
    exact h2
  have hg : IPChk.allR (Pts.glueIB K12.lits KW_12) 0 3 = true := by
    have h0 : IPChk.allR (Pts.glueIB K12.lits KW_12) 0 1 = true := kg_12_0
    have h1 : IPChk.allR (Pts.glueIB K12.lits KW_12) 0 2 = true := IPChk.allR_join (Pts.glueIB K12.lits KW_12) 0 1 1 h0 kg_12_1
    have h2 : IPChk.allR (Pts.glueIB K12.lits KW_12) 0 3 = true := IPChk.allR_join (Pts.glueIB K12.lits KW_12) 0 2 1 h1 kg_12_2
    exact h2
  have hlen : K12.lits.length = 3 := by decide
  intro k h1 h2
  obtain rfl : k = 12 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 12) K12.lits KW_12
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_6 : ∀ k, 13 ≤ k → k < 14 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 79 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 1 = true := kb_13_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 1 2 h0 kb_13_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 3 1 h1 kb_13_3
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 4 2 h2 kb_13_4
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 6 2 h3 kb_13_6
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 8 1 h4 kb_13_8
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 9 2 h5 kb_13_9
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 11 3 h6 kb_13_11
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 14 2 h7 kb_13_14
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 16 2 h8 kb_13_16
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 18 1 h9 kb_13_18
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 20 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 19 1 h10 kb_13_19
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 20 1 h11 kb_13_20
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 21 2 h12 kb_13_21
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 23 1 h13 kb_13_23
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 24 1 h14 kb_13_24
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 25 1 h15 kb_13_25
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 26 2 h16 kb_13_26
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 28 2 h17 kb_13_28
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 30 2 h18 kb_13_30
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 32 2 h19 kb_13_32
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 34 1 h20 kb_13_34
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 35 1 h21 kb_13_35
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 36 1 h22 kb_13_36
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 37 1 h23 kb_13_37
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 38 2 h24 kb_13_38
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 40 3 h25 kb_13_40
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 43 1 h26 kb_13_43
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 44 1 h27 kb_13_44
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 45 1 h28 kb_13_45
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 46 1 h29 kb_13_46
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 47 2 h30 kb_13_47
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 49 1 h31 kb_13_49
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 50 2 h32 kb_13_50
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 52 1 h33 kb_13_52
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 53 2 h34 kb_13_53
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 55 2 h35 kb_13_55
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 57 1 h36 kb_13_57
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 58 2 h37 kb_13_58
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 60 1 h38 kb_13_60
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 62 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 61 1 h39 kb_13_61
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 62 2 h40 kb_13_62
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 64 3 h41 kb_13_64
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 67 2 h42 kb_13_67
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 69 3 h43 kb_13_69
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 72 3 h44 kb_13_72
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 79 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K13.lits.getD i 0)) 0 75 4 h45 kb_13_75
    exact h46
  have hg : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 79 = true := by
    have h0 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 1 = true := kg_13_0
    have h1 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 3 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 1 2 h0 kg_13_1
    have h2 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 4 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 3 1 h1 kg_13_3
    have h3 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 6 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 4 2 h2 kg_13_4
    have h4 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 8 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 6 2 h3 kg_13_6
    have h5 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 9 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 8 1 h4 kg_13_8
    have h6 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 11 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 9 2 h5 kg_13_9
    have h7 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 14 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 11 3 h6 kg_13_11
    have h8 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 16 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 14 2 h7 kg_13_14
    have h9 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 18 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 16 2 h8 kg_13_16
    have h10 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 19 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 18 1 h9 kg_13_18
    have h11 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 20 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 19 1 h10 kg_13_19
    have h12 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 21 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 20 1 h11 kg_13_20
    have h13 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 23 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 21 2 h12 kg_13_21
    have h14 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 24 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 23 1 h13 kg_13_23
    have h15 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 25 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 24 1 h14 kg_13_24
    have h16 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 26 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 25 1 h15 kg_13_25
    have h17 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 28 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 26 2 h16 kg_13_26
    have h18 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 30 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 28 2 h17 kg_13_28
    have h19 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 32 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 30 2 h18 kg_13_30
    have h20 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 34 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 32 2 h19 kg_13_32
    have h21 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 35 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 34 1 h20 kg_13_34
    have h22 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 36 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 35 1 h21 kg_13_35
    have h23 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 37 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 36 1 h22 kg_13_36
    have h24 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 38 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 37 1 h23 kg_13_37
    have h25 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 40 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 38 2 h24 kg_13_38
    have h26 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 43 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 40 3 h25 kg_13_40
    have h27 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 44 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 43 1 h26 kg_13_43
    have h28 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 45 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 44 1 h27 kg_13_44
    have h29 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 46 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 45 1 h28 kg_13_45
    have h30 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 47 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 46 1 h29 kg_13_46
    have h31 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 49 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 47 2 h30 kg_13_47
    have h32 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 50 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 49 1 h31 kg_13_49
    have h33 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 52 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 50 2 h32 kg_13_50
    have h34 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 53 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 52 1 h33 kg_13_52
    have h35 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 55 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 53 2 h34 kg_13_53
    have h36 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 57 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 55 2 h35 kg_13_55
    have h37 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 58 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 57 1 h36 kg_13_57
    have h38 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 60 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 58 2 h37 kg_13_58
    have h39 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 61 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 60 1 h38 kg_13_60
    have h40 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 62 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 61 1 h39 kg_13_61
    have h41 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 64 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 62 2 h40 kg_13_62
    have h42 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 67 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 64 3 h41 kg_13_64
    have h43 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 69 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 67 2 h42 kg_13_67
    have h44 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 72 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 69 3 h43 kg_13_69
    have h45 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 75 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 72 3 h44 kg_13_72
    have h46 : IPChk.allR (Pts.glueIB K13.lits KW_13) 0 79 = true := IPChk.allR_join (Pts.glueIB K13.lits KW_13) 0 75 4 h45 kg_13_75
    exact h46
  have hlen : K13.lits.length = 79 := by decide
  intro k h1 h2
  obtain rfl : k = 13 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 13) K13.lits KW_13
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_7 : ∀ k, 14 ≤ k → k < 16 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_14 JW_14 14 2 jr_14
theorem jr6_8 : ∀ k, 16 ≤ k → k < 17 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 83 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 3 = true := kb_16_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 3 2 h0 kb_16_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 5 3 h1 kb_16_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 8 3 h2 kb_16_8
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 11 2 h3 kb_16_11
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 13 1 h4 kb_16_13
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 14 1 h5 kb_16_14
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 15 2 h6 kb_16_15
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 17 1 h7 kb_16_17
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 18 1 h8 kb_16_18
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 22 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 19 3 h9 kb_16_19
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 22 2 h10 kb_16_22
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 24 2 h11 kb_16_24
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 26 2 h12 kb_16_26
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 29 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 28 1 h13 kb_16_28
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 29 1 h14 kb_16_29
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 30 3 h15 kb_16_30
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 33 2 h16 kb_16_33
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 36 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 35 1 h17 kb_16_35
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 36 1 h18 kb_16_36
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 37 1 h19 kb_16_37
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 38 1 h20 kb_16_38
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 39 4 h21 kb_16_39
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 43 2 h22 kb_16_43
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 45 1 h23 kb_16_45
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 46 1 h24 kb_16_46
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 47 1 h25 kb_16_47
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 48 1 h26 kb_16_48
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 50 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 49 1 h27 kb_16_49
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 51 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 50 1 h28 kb_16_50
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 52 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 51 1 h29 kb_16_51
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 52 2 h30 kb_16_52
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 54 1 h31 kb_16_54
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 55 1 h32 kb_16_55
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 56 2 h33 kb_16_56
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 58 3 h34 kb_16_58
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 61 3 h35 kb_16_61
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 64 4 h36 kb_16_64
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 68 2 h37 kb_16_68
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 70 3 h38 kb_16_70
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 75 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 73 2 h39 kb_16_73
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 75 2 h40 kb_16_75
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 80 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 77 3 h41 kb_16_77
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 80 1 h42 kb_16_80
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K16.lits.getD i 0)) 0 81 2 h43 kb_16_81
    exact h44
  have hg : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 83 = true := by
    have h0 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 3 = true := kg_16_0
    have h1 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 5 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 3 2 h0 kg_16_3
    have h2 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 8 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 5 3 h1 kg_16_5
    have h3 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 11 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 8 3 h2 kg_16_8
    have h4 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 13 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 11 2 h3 kg_16_11
    have h5 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 14 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 13 1 h4 kg_16_13
    have h6 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 15 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 14 1 h5 kg_16_14
    have h7 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 17 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 15 2 h6 kg_16_15
    have h8 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 18 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 17 1 h7 kg_16_17
    have h9 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 19 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 18 1 h8 kg_16_18
    have h10 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 22 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 19 3 h9 kg_16_19
    have h11 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 24 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 22 2 h10 kg_16_22
    have h12 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 26 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 24 2 h11 kg_16_24
    have h13 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 28 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 26 2 h12 kg_16_26
    have h14 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 29 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 28 1 h13 kg_16_28
    have h15 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 30 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 29 1 h14 kg_16_29
    have h16 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 33 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 30 3 h15 kg_16_30
    have h17 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 35 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 33 2 h16 kg_16_33
    have h18 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 36 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 35 1 h17 kg_16_35
    have h19 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 37 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 36 1 h18 kg_16_36
    have h20 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 38 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 37 1 h19 kg_16_37
    have h21 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 39 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 38 1 h20 kg_16_38
    have h22 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 43 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 39 4 h21 kg_16_39
    have h23 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 45 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 43 2 h22 kg_16_43
    have h24 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 46 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 45 1 h23 kg_16_45
    have h25 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 47 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 46 1 h24 kg_16_46
    have h26 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 48 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 47 1 h25 kg_16_47
    have h27 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 49 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 48 1 h26 kg_16_48
    have h28 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 50 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 49 1 h27 kg_16_49
    have h29 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 51 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 50 1 h28 kg_16_50
    have h30 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 52 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 51 1 h29 kg_16_51
    have h31 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 54 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 52 2 h30 kg_16_52
    have h32 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 55 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 54 1 h31 kg_16_54
    have h33 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 56 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 55 1 h32 kg_16_55
    have h34 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 58 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 56 2 h33 kg_16_56
    have h35 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 61 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 58 3 h34 kg_16_58
    have h36 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 64 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 61 3 h35 kg_16_61
    have h37 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 68 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 64 4 h36 kg_16_64
    have h38 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 70 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 68 2 h37 kg_16_68
    have h39 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 73 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 70 3 h38 kg_16_70
    have h40 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 75 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 73 2 h39 kg_16_73
    have h41 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 77 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 75 2 h40 kg_16_75
    have h42 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 80 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 77 3 h41 kg_16_77
    have h43 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 81 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 80 1 h42 kg_16_80
    have h44 : IPChk.allR (Pts.glueIB K16.lits KW_16) 0 83 = true := IPChk.allR_join (Pts.glueIB K16.lits KW_16) 0 81 2 h43 kg_16_81
    exact h44
  have hlen : K16.lits.length = 83 := by decide
  intro k h1 h2
  obtain rfl : k = 16 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 16) K16.lits KW_16
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_9 : ∀ k, 17 ≤ k → k < 18 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_17 JW_17 17 1 jr_17
theorem jr6_10 : ∀ k, 18 ≤ k → k < 19 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 6 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 3 = true := kb_18_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 3 2 h0 kb_18_3
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K18.lits.getD i 0)) 0 5 1 h1 kb_18_5
    exact h2
  have hg : IPChk.allR (Pts.glueIB K18.lits KW_18) 0 6 = true := by
    have h0 : IPChk.allR (Pts.glueIB K18.lits KW_18) 0 3 = true := kg_18_0
    have h1 : IPChk.allR (Pts.glueIB K18.lits KW_18) 0 5 = true := IPChk.allR_join (Pts.glueIB K18.lits KW_18) 0 3 2 h0 kg_18_3
    have h2 : IPChk.allR (Pts.glueIB K18.lits KW_18) 0 6 = true := IPChk.allR_join (Pts.glueIB K18.lits KW_18) 0 5 1 h1 kg_18_5
    exact h2
  have hlen : K18.lits.length = 6 := by decide
  intro k h1 h2
  obtain rfl : k = 18 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 18) K18.lits KW_18
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_11 : ∀ k, 19 ≤ k → k < 43 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_19 JW_19 19 24 jr_19
theorem jr6_12 : ∀ k, 43 ≤ k → k < 44 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 19 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 1 = true := kb_43_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 1 1 h0 kb_43_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 2 1 h1 kb_43_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 3 1 h2 kb_43_3
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 4 1 h3 kb_43_4
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 5 1 h4 kb_43_5
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 6 1 h5 kb_43_6
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 7 1 h6 kb_43_7
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 8 1 h7 kb_43_8
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 9 2 h8 kb_43_9
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 11 3 h9 kb_43_11
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 14 1 h10 kb_43_14
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 15 1 h11 kb_43_15
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 16 1 h12 kb_43_16
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 18 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 17 1 h13 kb_43_17
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 19 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K43.lits.getD i 0)) 0 18 1 h14 kb_43_18
    exact h15
  have hg : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 19 = true := by
    have h0 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 1 = true := kg_43_0
    have h1 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 2 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 1 1 h0 kg_43_1
    have h2 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 3 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 2 1 h1 kg_43_2
    have h3 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 4 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 3 1 h2 kg_43_3
    have h4 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 5 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 4 1 h3 kg_43_4
    have h5 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 6 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 5 1 h4 kg_43_5
    have h6 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 7 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 6 1 h5 kg_43_6
    have h7 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 8 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 7 1 h6 kg_43_7
    have h8 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 9 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 8 1 h7 kg_43_8
    have h9 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 11 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 9 2 h8 kg_43_9
    have h10 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 14 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 11 3 h9 kg_43_11
    have h11 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 15 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 14 1 h10 kg_43_14
    have h12 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 16 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 15 1 h11 kg_43_15
    have h13 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 17 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 16 1 h12 kg_43_16
    have h14 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 18 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 17 1 h13 kg_43_17
    have h15 : IPChk.allR (Pts.glueIB K43.lits KW_43) 0 19 = true := IPChk.allR_join (Pts.glueIB K43.lits KW_43) 0 18 1 h14 kg_43_18
    exact h15
  have hlen : K43.lits.length = 19 := by decide
  intro k h1 h2
  obtain rfl : k = 43 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 43) K43.lits KW_43
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_13 : ∀ k, 44 ≤ k → k < 71 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_44 JW_44 44 27 jr_44
theorem jr6_14 : ∀ k, 71 ≤ k → k < 91 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_44 JW_44 71 20 jr_71
theorem jr6_15 : ∀ k, 91 ≤ k → k < 92 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6508 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1 = true := kb_91_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1 3 h0 kb_91_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4 8 h1 kb_91_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 12 5 h2 kb_91_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 23 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 17 6 h3 kb_91_17
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 23 2 h4 kb_91_23
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 25 5 h5 kb_91_25
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 30 23 h6 kb_91_30
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 53 3 h7 kb_91_53
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 56 4 h8 kb_91_56
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 60 8 h9 kb_91_60
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 68 14 h10 kb_91_68
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 82 2 h11 kb_91_82
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 84 5 h12 kb_91_84
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 96 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 89 7 h13 kb_91_89
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 96 17 h14 kb_91_96
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 113 3 h15 kb_91_113
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 116 15 h16 kb_91_116
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 131 3 h17 kb_91_131
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 134 3 h18 kb_91_134
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 137 18 h19 kb_91_137
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 155 3 h20 kb_91_155
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 158 1 h21 kb_91_158
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 159 52 h22 kb_91_159
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 211 2 h23 kb_91_211
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 222 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 213 9 h24 kb_91_213
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 222 1 h25 kb_91_222
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 223 18 h26 kb_91_223
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 270 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 241 29 h27 kb_91_241
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 270 2 h28 kb_91_270
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 298 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 272 26 h29 kb_91_272
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 298 67 h30 kb_91_298
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 365 37 h31 kb_91_365
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 403 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 402 1 h32 kb_91_402
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 404 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 403 1 h33 kb_91_403
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 407 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 404 3 h34 kb_91_404
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 407 2 h35 kb_91_407
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 409 1 h36 kb_91_409
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 419 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 410 9 h37 kb_91_410
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 424 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 419 5 h38 kb_91_419
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 427 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 424 3 h39 kb_91_424
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 432 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 427 5 h40 kb_91_427
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 432 11 h41 kb_91_432
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 443 1 h42 kb_91_443
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 453 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 444 9 h43 kb_91_444
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 455 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 453 2 h44 kb_91_453
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 468 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 455 13 h45 kb_91_455
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 528 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 468 60 h46 kb_91_468
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 528 23 h47 kb_91_528
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 552 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 551 1 h48 kb_91_551
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 555 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 552 3 h49 kb_91_552
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 555 2 h50 kb_91_555
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 558 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 557 1 h51 kb_91_557
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 558 9 h52 kb_91_558
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 569 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 567 2 h53 kb_91_567
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 572 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 569 3 h54 kb_91_569
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 575 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 572 3 h55 kb_91_572
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 575 1 h56 kb_91_575
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 585 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 576 9 h57 kb_91_576
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 589 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 585 4 h58 kb_91_585
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 592 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 589 3 h59 kb_91_589
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 606 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 592 14 h60 kb_91_592
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 606 3 h61 kb_91_606
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 619 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 609 10 h62 kb_91_609
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 619 17 h63 kb_91_619
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 642 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 636 6 h64 kb_91_636
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 650 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 642 8 h65 kb_91_642
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 650 31 h66 kb_91_650
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 681 3 h67 kb_91_681
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 684 1 h68 kb_91_684
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 685 11 h69 kb_91_685
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 725 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 696 29 h70 kb_91_696
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 725 17 h71 kb_91_725
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 806 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 742 64 h72 kb_91_742
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 808 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 806 2 h73 kb_91_806
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 809 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 808 1 h74 kb_91_808
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 809 18 h75 kb_91_809
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 827 2 h76 kb_91_827
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 829 1 h77 kb_91_829
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 840 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 830 10 h78 kb_91_830
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 840 37 h79 kb_91_840
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 947 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 877 70 h80 kb_91_877
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 947 2 h81 kb_91_947
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 950 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 949 1 h82 kb_91_949
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 951 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 950 1 h83 kb_91_950
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 959 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 951 8 h84 kb_91_951
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 960 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 959 1 h85 kb_91_959
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 981 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 960 21 h86 kb_91_960
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 982 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 981 1 h87 kb_91_981
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 987 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 982 5 h88 kb_91_982
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 992 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 987 5 h89 kb_91_987
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 992 80 h90 kb_91_992
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1072 36 h91 kb_91_1072
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1108 29 h92 kb_91_1108
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1137 17 h93 kb_91_1137
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1215 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1154 61 h94 kb_91_1154
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1216 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1215 1 h95 kb_91_1215
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1226 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1216 10 h96 kb_91_1216
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1263 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1226 37 h97 kb_91_1226
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1263 94 h98 kb_91_1263
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1357 32 h99 kb_91_1357
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1391 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1389 2 h100 kb_91_1389
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1391 25 h101 kb_91_1391
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1418 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1416 2 h102 kb_91_1416
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1418 30 h103 kb_91_1418
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1450 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1448 2 h104 kb_91_1448
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1482 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1450 32 h105 kb_91_1450
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1491 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1482 9 h106 kb_91_1482
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1492 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1491 1 h107 kb_91_1491
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1494 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1492 2 h108 kb_91_1492
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1494 1 h109 kb_91_1494
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1500 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1495 5 h110 kb_91_1495
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1500 2 h111 kb_91_1500
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1503 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1502 1 h112 kb_91_1502
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1503 4 h113 kb_91_1503
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1507 1 h114 kb_91_1507
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1508 78 h115 kb_91_1508
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1639 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1586 53 h116 kb_91_1586
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1656 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1639 17 h117 kb_91_1639
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1658 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1656 2 h118 kb_91_1656
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1659 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1658 1 h119 kb_91_1658
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1659 4 h120 kb_91_1659
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1664 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1663 1 h121 kb_91_1663
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1667 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1664 3 h122 kb_91_1664
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1667 1 h123 kb_91_1667
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1690 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1668 22 h124 kb_91_1668
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1714 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1690 24 h125 kb_91_1690
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1714 28 h126 kb_91_1714
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1804 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1742 62 h127 kb_91_1742
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1819 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1804 15 h128 kb_91_1804
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1819 1 h129 kb_91_1819
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1820 3 h130 kb_91_1820
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1859 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1823 36 h131 kb_91_1823
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1864 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1859 5 h132 kb_91_1859
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1868 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1864 4 h133 kb_91_1864
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1868 1 h134 kb_91_1868
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1869 8 h135 kb_91_1869
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1877 1 h136 kb_91_1877
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1883 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1878 5 h137 kb_91_1878
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1904 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1883 21 h138 kb_91_1883
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1904 10 h139 kb_91_1904
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1914 6 h140 kb_91_1914
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1922 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1920 2 h141 kb_91_1920
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1944 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1922 22 h142 kb_91_1922
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1983 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1944 39 h143 kb_91_1944
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2006 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1983 23 h144 kb_91_1983
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2023 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2006 17 h145 kb_91_2006
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2024 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2023 1 h146 kb_91_2023
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2025 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2024 1 h147 kb_91_2024
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2026 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2025 1 h148 kb_91_2025
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2029 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2026 3 h149 kb_91_2026
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2030 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2029 1 h150 kb_91_2029
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2034 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2030 4 h151 kb_91_2030
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2035 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2034 1 h152 kb_91_2034
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2040 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2035 5 h153 kb_91_2035
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2040 29 h154 kb_91_2040
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2069 2 h155 kb_91_2069
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2079 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2071 8 h156 kb_91_2071
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2079 22 h157 kb_91_2079
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2101 57 h158 kb_91_2101
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2158 14 h159 kb_91_2158
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2172 3 h160 kb_91_2172
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2175 1 h161 kb_91_2175
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2176 24 h162 kb_91_2176
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2200 5 h163 kb_91_2200
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2205 8 h164 kb_91_2205
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2249 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2213 36 h165 kb_91_2213
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2249 2 h166 kb_91_2249
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2251 9 h167 kb_91_2251
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2260 59 h168 kb_91_2260
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2319 25 h169 kb_91_2319
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2344 12 h170 kb_91_2344
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2356 15 h171 kb_91_2356
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2371 38 h172 kb_91_2371
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2409 4 h173 kb_91_2409
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2413 2 h174 kb_91_2413
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2415 6 h175 kb_91_2415
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2525 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2421 104 h176 kb_91_2421
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2554 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2525 29 h177 kb_91_2525
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2561 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2554 7 h178 kb_91_2554
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2579 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2561 18 h179 kb_91_2561
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2586 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2579 7 h180 kb_91_2579
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2636 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2586 50 h181 kb_91_2586
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2706 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2636 70 h182 kb_91_2636
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2710 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2706 4 h183 kb_91_2706
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2813 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2710 103 h184 kb_91_2710
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2861 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2813 48 h185 kb_91_2813
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2861 1 h186 kb_91_2861
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2862 13 h187 kb_91_2862
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2876 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2875 1 h188 kb_91_2875
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2876 10 h189 kb_91_2876
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2891 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2886 5 h190 kb_91_2886
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2942 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2891 51 h191 kb_91_2891
    have h193 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3009 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 2942 67 h192 kb_91_2942
    have h194 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3013 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3009 4 h193 kb_91_3009
    have h195 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3018 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3013 5 h194 kb_91_3013
    have h196 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3018 105 h195 kb_91_3018
    have h197 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3123 19 h196 kb_91_3123
    have h198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3142 1 h197 kb_91_3142
    have h199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3143 7 h198 kb_91_3143
    have h200 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3150 28 h199 kb_91_3150
    have h201 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3225 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3178 47 h200 kb_91_3178
    have h202 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3225 51 h201 kb_91_3225
    have h203 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3276 44 h202 kb_91_3276
    have h204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3321 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3320 1 h203 kb_91_3320
    have h205 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3321 13 h204 kb_91_3321
    have h206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3354 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3334 20 h205 kb_91_3334
    have h207 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3354 18 h206 kb_91_3354
    have h208 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3372 8 h207 kb_91_3372
    have h209 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3431 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3380 51 h208 kb_91_3380
    have h210 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3537 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3431 106 h209 kb_91_3431
    have h211 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3548 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3537 11 h210 kb_91_3537
    have h212 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3548 19 h211 kb_91_3548
    have h213 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3602 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3567 35 h212 kb_91_3567
    have h214 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3602 64 h213 kb_91_3602
    have h215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3666 31 h214 kb_91_3666
    have h216 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3714 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3697 17 h215 kb_91_3697
    have h217 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3714 75 h216 kb_91_3714
    have h218 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3792 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3789 3 h217 kb_91_3789
    have h219 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3821 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3792 29 h218 kb_91_3792
    have h220 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3823 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3821 2 h219 kb_91_3821
    have h221 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3829 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3823 6 h220 kb_91_3823
    have h222 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3831 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3829 2 h221 kb_91_3829
    have h223 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3853 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3831 22 h222 kb_91_3831
    have h224 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3913 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3853 60 h223 kb_91_3853
    have h225 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3917 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3913 4 h224 kb_91_3913
    have h226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3917 4 h225 kb_91_3917
    have h227 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3933 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3921 12 h226 kb_91_3921
    have h228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4053 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 3933 120 h227 kb_91_3933
    have h229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4053 111 h228 kb_91_4053
    have h230 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4169 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4164 5 h229 kb_91_4164
    have h231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4180 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4169 11 h230 kb_91_4169
    have h232 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4251 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4180 71 h231 kb_91_4180
    have h233 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4251 86 h232 kb_91_4251
    have h234 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4337 84 h233 kb_91_4337
    have h235 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4437 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4421 16 h234 kb_91_4421
    have h236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4495 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4437 58 h235 kb_91_4437
    have h237 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4497 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4495 2 h236 kb_91_4495
    have h238 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4501 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4497 4 h237 kb_91_4497
    have h239 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4502 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4501 1 h238 kb_91_4501
    have h240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4502 5 h239 kb_91_4502
    have h241 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4507 4 h240 kb_91_4507
    have h242 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4512 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4511 1 h241 kb_91_4511
    have h243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4519 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4512 7 h242 kb_91_4512
    have h244 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4519 121 h243 kb_91_4519
    have h245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4640 15 h244 kb_91_4640
    have h246 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4771 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4655 116 h245 kb_91_4655
    have h247 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4780 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4771 9 h246 kb_91_4771
    have h248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4780 11 h247 kb_91_4780
    have h249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4791 5 h248 kb_91_4791
    have h250 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4796 1 h249 kb_91_4796
    have h251 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4811 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4797 14 h250 kb_91_4797
    have h252 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4812 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4811 1 h251 kb_91_4811
    have h253 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4844 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4812 32 h252 kb_91_4812
    have h254 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4855 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4844 11 h253 kb_91_4844
    have h255 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4855 7 h254 kb_91_4855
    have h256 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4863 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4862 1 h255 kb_91_4862
    have h257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4875 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4863 12 h256 kb_91_4863
    have h258 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4984 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4875 109 h257 kb_91_4875
    have h259 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4993 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4984 9 h258 kb_91_4984
    have h260 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 4993 117 h259 kb_91_4993
    have h261 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5110 14 h260 kb_91_5110
    have h262 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5124 11 h261 kb_91_5124
    have h263 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5138 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5135 3 h262 kb_91_5135
    have h264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5138 32 h263 kb_91_5138
    have h265 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5181 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5170 11 h264 kb_91_5170
    have h266 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5181 2 h265 kb_91_5181
    have h267 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5183 1 h266 kb_91_5183
    have h268 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5184 10 h267 kb_91_5184
    have h269 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5194 52 h268 kb_91_5194
    have h270 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5307 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5246 61 h269 kb_91_5246
    have h271 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5307 45 h270 kb_91_5307
    have h272 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5352 4 h271 kb_91_5352
    have h273 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5369 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5356 13 h272 kb_91_5356
    have h274 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5369 12 h273 kb_91_5369
    have h275 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5395 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5381 14 h274 kb_91_5381
    have h276 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5395 17 h275 kb_91_5395
    have h277 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5444 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5412 32 h276 kb_91_5412
    have h278 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5444 30 h277 kb_91_5444
    have h279 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5475 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5474 1 h278 kb_91_5474
    have h280 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5475 39 h279 kb_91_5475
    have h281 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5515 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5514 1 h280 kb_91_5514
    have h282 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5538 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5515 23 h281 kb_91_5515
    have h283 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5566 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5538 28 h282 kb_91_5538
    have h284 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5566 1 h283 kb_91_5566
    have h285 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5597 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5567 30 h284 kb_91_5567
    have h286 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5598 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5597 1 h285 kb_91_5597
    have h287 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5610 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5598 12 h286 kb_91_5598
    have h288 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5611 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5610 1 h287 kb_91_5610
    have h289 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5640 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5611 29 h288 kb_91_5611
    have h290 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5640 13 h289 kb_91_5640
    have h291 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5653 1 h290 kb_91_5653
    have h292 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5655 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5654 1 h291 kb_91_5654
    have h293 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5655 33 h292 kb_91_5655
    have h294 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5688 1 h293 kb_91_5688
    have h295 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5697 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5689 8 h294 kb_91_5689
    have h296 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5697 37 h295 kb_91_5697
    have h297 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5735 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5734 1 h296 kb_91_5734
    have h298 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5735 7 h297 kb_91_5735
    have h299 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5744 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5742 2 h298 kb_91_5742
    have h300 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5772 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5744 28 h299 kb_91_5744
    have h301 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5870 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5772 98 h300 kb_91_5772
    have h302 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5877 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5870 7 h301 kb_91_5870
    have h303 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5877 1 h302 kb_91_5877
    have h304 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5881 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5878 3 h303 kb_91_5878
    have h305 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5882 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5881 1 h304 kb_91_5881
    have h306 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5887 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5882 5 h305 kb_91_5882
    have h307 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5888 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5887 1 h306 kb_91_5887
    have h308 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5899 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5888 11 h307 kb_91_5888
    have h309 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5919 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5899 20 h308 kb_91_5899
    have h310 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5926 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5919 7 h309 kb_91_5919
    have h311 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5955 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5926 29 h310 kb_91_5926
    have h312 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5968 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5955 13 h311 kb_91_5955
    have h313 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5978 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5968 10 h312 kb_91_5968
    have h314 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5995 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5978 17 h313 kb_91_5978
    have h315 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6023 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 5995 28 h314 kb_91_5995
    have h316 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6028 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6023 5 h315 kb_91_6023
    have h317 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6028 15 h316 kb_91_6028
    have h318 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6044 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6043 1 h317 kb_91_6043
    have h319 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6045 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6044 1 h318 kb_91_6044
    have h320 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6047 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6045 2 h319 kb_91_6045
    have h321 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6052 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6047 5 h320 kb_91_6047
    have h322 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6053 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6052 1 h321 kb_91_6052
    have h323 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6056 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6053 3 h322 kb_91_6053
    have h324 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6057 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6056 1 h323 kb_91_6056
    have h325 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6060 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6057 3 h324 kb_91_6057
    have h326 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6060 8 h325 kb_91_6060
    have h327 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6068 1 h326 kb_91_6068
    have h328 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6075 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6069 6 h327 kb_91_6069
    have h329 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6076 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6075 1 h328 kb_91_6075
    have h330 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6081 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6076 5 h329 kb_91_6076
    have h331 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6081 22 h330 kb_91_6081
    have h332 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6103 26 h331 kb_91_6103
    have h333 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6129 5 h332 kb_91_6129
    have h334 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6134 13 h333 kb_91_6134
    have h335 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6147 7 h334 kb_91_6147
    have h336 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6154 31 h335 kb_91_6154
    have h337 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6185 1 h336 kb_91_6185
    have h338 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6186 1 h337 kb_91_6186
    have h339 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6187 1 h338 kb_91_6187
    have h340 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6188 5 h339 kb_91_6188
    have h341 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6193 1 h340 kb_91_6193
    have h342 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6194 7 h341 kb_91_6194
    have h343 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6201 8 h342 kb_91_6201
    have h344 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6232 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6209 23 h343 kb_91_6209
    have h345 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6232 22 h344 kb_91_6232
    have h346 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6273 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6254 19 h345 kb_91_6254
    have h347 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6273 1 h346 kb_91_6273
    have h348 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6276 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6274 2 h347 kb_91_6274
    have h349 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6276 37 h348 kb_91_6276
    have h350 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6330 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6313 17 h349 kb_91_6313
    have h351 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6330 1 h350 kb_91_6330
    have h352 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6360 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6331 29 h351 kb_91_6331
    have h353 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6380 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6360 20 h352 kb_91_6360
    have h354 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6380 3 h353 kb_91_6380
    have h355 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6388 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6383 5 h354 kb_91_6383
    have h356 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6388 21 h355 kb_91_6388
    have h357 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6438 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6409 29 h356 kb_91_6409
    have h358 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6438 1 h357 kb_91_6438
    have h359 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6454 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6439 15 h358 kb_91_6439
    have h360 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6473 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6454 19 h359 kb_91_6454
    have h361 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6473 6 h360 kb_91_6473
    have h362 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6479 1 h361 kb_91_6479
    have h363 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6481 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6480 1 h362 kb_91_6480
    have h364 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6481 5 h363 kb_91_6481
    have h365 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6504 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6486 18 h364 kb_91_6486
    have h366 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6507 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6504 3 h365 kb_91_6504
    have h367 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 6507 1 h366 kb_91_6507
    exact h367
  have hg : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6508 = true := by
    have h0 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1 = true := kg_91_0
    have h1 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1 3 h0 kg_91_1
    have h2 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 12 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4 8 h1 kg_91_4
    have h3 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 17 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 12 5 h2 kg_91_12
    have h4 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 23 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 17 6 h3 kg_91_17
    have h5 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 25 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 23 2 h4 kg_91_23
    have h6 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 30 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 25 5 h5 kg_91_25
    have h7 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 53 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 30 23 h6 kg_91_30
    have h8 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 56 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 53 3 h7 kg_91_53
    have h9 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 60 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 56 4 h8 kg_91_56
    have h10 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 68 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 60 8 h9 kg_91_60
    have h11 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 82 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 68 14 h10 kg_91_68
    have h12 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 84 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 82 2 h11 kg_91_82
    have h13 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 89 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 84 5 h12 kg_91_84
    have h14 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 96 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 89 7 h13 kg_91_89
    have h15 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 113 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 96 17 h14 kg_91_96
    have h16 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 116 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 113 3 h15 kg_91_113
    have h17 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 131 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 116 15 h16 kg_91_116
    have h18 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 134 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 131 3 h17 kg_91_131
    have h19 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 137 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 134 3 h18 kg_91_134
    have h20 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 155 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 137 18 h19 kg_91_137
    have h21 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 158 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 155 3 h20 kg_91_155
    have h22 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 159 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 158 1 h21 kg_91_158
    have h23 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 211 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 159 52 h22 kg_91_159
    have h24 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 213 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 211 2 h23 kg_91_211
    have h25 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 222 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 213 9 h24 kg_91_213
    have h26 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 223 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 222 1 h25 kg_91_222
    have h27 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 241 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 223 18 h26 kg_91_223
    have h28 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 270 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 241 29 h27 kg_91_241
    have h29 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 272 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 270 2 h28 kg_91_270
    have h30 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 298 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 272 26 h29 kg_91_272
    have h31 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 365 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 298 67 h30 kg_91_298
    have h32 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 402 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 365 37 h31 kg_91_365
    have h33 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 403 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 402 1 h32 kg_91_402
    have h34 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 404 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 403 1 h33 kg_91_403
    have h35 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 407 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 404 3 h34 kg_91_404
    have h36 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 409 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 407 2 h35 kg_91_407
    have h37 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 410 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 409 1 h36 kg_91_409
    have h38 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 419 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 410 9 h37 kg_91_410
    have h39 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 424 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 419 5 h38 kg_91_419
    have h40 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 427 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 424 3 h39 kg_91_424
    have h41 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 432 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 427 5 h40 kg_91_427
    have h42 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 443 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 432 11 h41 kg_91_432
    have h43 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 444 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 443 1 h42 kg_91_443
    have h44 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 453 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 444 9 h43 kg_91_444
    have h45 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 455 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 453 2 h44 kg_91_453
    have h46 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 468 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 455 13 h45 kg_91_455
    have h47 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 528 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 468 60 h46 kg_91_468
    have h48 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 551 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 528 23 h47 kg_91_528
    have h49 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 552 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 551 1 h48 kg_91_551
    have h50 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 555 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 552 3 h49 kg_91_552
    have h51 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 557 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 555 2 h50 kg_91_555
    have h52 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 558 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 557 1 h51 kg_91_557
    have h53 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 567 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 558 9 h52 kg_91_558
    have h54 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 569 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 567 2 h53 kg_91_567
    have h55 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 572 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 569 3 h54 kg_91_569
    have h56 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 575 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 572 3 h55 kg_91_572
    have h57 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 576 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 575 1 h56 kg_91_575
    have h58 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 585 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 576 9 h57 kg_91_576
    have h59 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 589 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 585 4 h58 kg_91_585
    have h60 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 592 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 589 3 h59 kg_91_589
    have h61 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 606 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 592 14 h60 kg_91_592
    have h62 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 609 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 606 3 h61 kg_91_606
    have h63 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 619 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 609 10 h62 kg_91_609
    have h64 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 636 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 619 17 h63 kg_91_619
    have h65 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 642 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 636 6 h64 kg_91_636
    have h66 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 650 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 642 8 h65 kg_91_642
    have h67 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 681 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 650 31 h66 kg_91_650
    have h68 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 684 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 681 3 h67 kg_91_681
    have h69 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 685 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 684 1 h68 kg_91_684
    have h70 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 696 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 685 11 h69 kg_91_685
    have h71 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 725 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 696 29 h70 kg_91_696
    have h72 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 742 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 725 17 h71 kg_91_725
    have h73 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 806 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 742 64 h72 kg_91_742
    have h74 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 808 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 806 2 h73 kg_91_806
    have h75 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 809 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 808 1 h74 kg_91_808
    have h76 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 827 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 809 18 h75 kg_91_809
    have h77 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 829 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 827 2 h76 kg_91_827
    have h78 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 830 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 829 1 h77 kg_91_829
    have h79 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 840 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 830 10 h78 kg_91_830
    have h80 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 877 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 840 37 h79 kg_91_840
    have h81 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 947 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 877 70 h80 kg_91_877
    have h82 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 949 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 947 2 h81 kg_91_947
    have h83 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 950 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 949 1 h82 kg_91_949
    have h84 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 951 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 950 1 h83 kg_91_950
    have h85 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 959 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 951 8 h84 kg_91_951
    have h86 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 960 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 959 1 h85 kg_91_959
    have h87 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 981 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 960 21 h86 kg_91_960
    have h88 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 982 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 981 1 h87 kg_91_981
    have h89 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 987 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 982 5 h88 kg_91_982
    have h90 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 992 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 987 5 h89 kg_91_987
    have h91 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1072 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 992 80 h90 kg_91_992
    have h92 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1108 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1072 36 h91 kg_91_1072
    have h93 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1137 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1108 29 h92 kg_91_1108
    have h94 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1154 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1137 17 h93 kg_91_1137
    have h95 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1215 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1154 61 h94 kg_91_1154
    have h96 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1216 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1215 1 h95 kg_91_1215
    have h97 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1226 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1216 10 h96 kg_91_1216
    have h98 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1263 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1226 37 h97 kg_91_1226
    have h99 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1357 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1263 94 h98 kg_91_1263
    have h100 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1389 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1357 32 h99 kg_91_1357
    have h101 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1391 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1389 2 h100 kg_91_1389
    have h102 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1416 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1391 25 h101 kg_91_1391
    have h103 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1418 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1416 2 h102 kg_91_1416
    have h104 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1448 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1418 30 h103 kg_91_1418
    have h105 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1450 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1448 2 h104 kg_91_1448
    have h106 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1482 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1450 32 h105 kg_91_1450
    have h107 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1491 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1482 9 h106 kg_91_1482
    have h108 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1492 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1491 1 h107 kg_91_1491
    have h109 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1494 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1492 2 h108 kg_91_1492
    have h110 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1495 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1494 1 h109 kg_91_1494
    have h111 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1500 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1495 5 h110 kg_91_1495
    have h112 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1502 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1500 2 h111 kg_91_1500
    have h113 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1503 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1502 1 h112 kg_91_1502
    have h114 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1507 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1503 4 h113 kg_91_1503
    have h115 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1508 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1507 1 h114 kg_91_1507
    have h116 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1586 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1508 78 h115 kg_91_1508
    have h117 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1639 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1586 53 h116 kg_91_1586
    have h118 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1656 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1639 17 h117 kg_91_1639
    have h119 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1658 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1656 2 h118 kg_91_1656
    have h120 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1659 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1658 1 h119 kg_91_1658
    have h121 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1663 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1659 4 h120 kg_91_1659
    have h122 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1664 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1663 1 h121 kg_91_1663
    have h123 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1667 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1664 3 h122 kg_91_1664
    have h124 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1668 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1667 1 h123 kg_91_1667
    have h125 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1690 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1668 22 h124 kg_91_1668
    have h126 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1714 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1690 24 h125 kg_91_1690
    have h127 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1742 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1714 28 h126 kg_91_1714
    have h128 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1804 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1742 62 h127 kg_91_1742
    have h129 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1819 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1804 15 h128 kg_91_1804
    have h130 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1820 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1819 1 h129 kg_91_1819
    have h131 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1823 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1820 3 h130 kg_91_1820
    have h132 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1859 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1823 36 h131 kg_91_1823
    have h133 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1864 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1859 5 h132 kg_91_1859
    have h134 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1868 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1864 4 h133 kg_91_1864
    have h135 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1869 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1868 1 h134 kg_91_1868
    have h136 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1877 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1869 8 h135 kg_91_1869
    have h137 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1878 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1877 1 h136 kg_91_1877
    have h138 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1883 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1878 5 h137 kg_91_1878
    have h139 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1904 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1883 21 h138 kg_91_1883
    have h140 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1914 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1904 10 h139 kg_91_1904
    have h141 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1920 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1914 6 h140 kg_91_1914
    have h142 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1922 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1920 2 h141 kg_91_1920
    have h143 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1944 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1922 22 h142 kg_91_1922
    have h144 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1983 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1944 39 h143 kg_91_1944
    have h145 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2006 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 1983 23 h144 kg_91_1983
    have h146 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2023 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2006 17 h145 kg_91_2006
    have h147 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2024 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2023 1 h146 kg_91_2023
    have h148 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2025 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2024 1 h147 kg_91_2024
    have h149 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2026 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2025 1 h148 kg_91_2025
    have h150 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2029 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2026 3 h149 kg_91_2026
    have h151 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2030 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2029 1 h150 kg_91_2029
    have h152 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2034 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2030 4 h151 kg_91_2030
    have h153 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2035 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2034 1 h152 kg_91_2034
    have h154 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2040 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2035 5 h153 kg_91_2035
    have h155 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2069 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2040 29 h154 kg_91_2040
    have h156 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2071 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2069 2 h155 kg_91_2069
    have h157 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2079 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2071 8 h156 kg_91_2071
    have h158 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2101 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2079 22 h157 kg_91_2079
    have h159 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2158 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2101 57 h158 kg_91_2101
    have h160 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2172 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2158 14 h159 kg_91_2158
    have h161 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2175 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2172 3 h160 kg_91_2172
    have h162 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2176 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2175 1 h161 kg_91_2175
    have h163 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2200 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2176 24 h162 kg_91_2176
    have h164 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2205 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2200 5 h163 kg_91_2200
    have h165 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2213 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2205 8 h164 kg_91_2205
    have h166 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2249 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2213 36 h165 kg_91_2213
    have h167 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2251 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2249 2 h166 kg_91_2249
    have h168 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2260 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2251 9 h167 kg_91_2251
    have h169 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2319 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2260 59 h168 kg_91_2260
    have h170 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2344 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2319 25 h169 kg_91_2319
    have h171 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2356 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2344 12 h170 kg_91_2344
    have h172 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2371 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2356 15 h171 kg_91_2356
    have h173 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2409 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2371 38 h172 kg_91_2371
    have h174 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2413 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2409 4 h173 kg_91_2409
    have h175 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2415 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2413 2 h174 kg_91_2413
    have h176 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2421 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2415 6 h175 kg_91_2415
    have h177 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2525 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2421 104 h176 kg_91_2421
    have h178 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2554 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2525 29 h177 kg_91_2525
    have h179 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2561 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2554 7 h178 kg_91_2554
    have h180 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2579 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2561 18 h179 kg_91_2561
    have h181 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2586 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2579 7 h180 kg_91_2579
    have h182 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2636 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2586 50 h181 kg_91_2586
    have h183 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2706 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2636 70 h182 kg_91_2636
    have h184 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2710 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2706 4 h183 kg_91_2706
    have h185 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2813 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2710 103 h184 kg_91_2710
    have h186 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2861 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2813 48 h185 kg_91_2813
    have h187 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2862 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2861 1 h186 kg_91_2861
    have h188 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2875 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2862 13 h187 kg_91_2862
    have h189 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2876 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2875 1 h188 kg_91_2875
    have h190 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2886 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2876 10 h189 kg_91_2876
    have h191 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2891 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2886 5 h190 kg_91_2886
    have h192 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 2942 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2891 51 h191 kg_91_2891
    have h193 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3009 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 2942 67 h192 kg_91_2942
    have h194 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3013 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3009 4 h193 kg_91_3009
    have h195 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3018 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3013 5 h194 kg_91_3013
    have h196 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3123 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3018 105 h195 kg_91_3018
    have h197 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3142 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3123 19 h196 kg_91_3123
    have h198 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3143 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3142 1 h197 kg_91_3142
    have h199 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3150 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3143 7 h198 kg_91_3143
    have h200 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3178 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3150 28 h199 kg_91_3150
    have h201 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3225 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3178 47 h200 kg_91_3178
    have h202 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3276 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3225 51 h201 kg_91_3225
    have h203 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3320 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3276 44 h202 kg_91_3276
    have h204 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3321 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3320 1 h203 kg_91_3320
    have h205 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3334 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3321 13 h204 kg_91_3321
    have h206 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3354 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3334 20 h205 kg_91_3334
    have h207 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3372 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3354 18 h206 kg_91_3354
    have h208 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3380 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3372 8 h207 kg_91_3372
    have h209 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3431 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3380 51 h208 kg_91_3380
    have h210 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3537 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3431 106 h209 kg_91_3431
    have h211 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3548 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3537 11 h210 kg_91_3537
    have h212 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3567 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3548 19 h211 kg_91_3548
    have h213 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3602 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3567 35 h212 kg_91_3567
    have h214 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3666 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3602 64 h213 kg_91_3602
    have h215 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3697 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3666 31 h214 kg_91_3666
    have h216 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3714 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3697 17 h215 kg_91_3697
    have h217 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3789 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3714 75 h216 kg_91_3714
    have h218 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3792 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3789 3 h217 kg_91_3789
    have h219 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3821 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3792 29 h218 kg_91_3792
    have h220 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3823 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3821 2 h219 kg_91_3821
    have h221 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3829 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3823 6 h220 kg_91_3823
    have h222 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3831 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3829 2 h221 kg_91_3829
    have h223 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3853 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3831 22 h222 kg_91_3831
    have h224 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3913 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3853 60 h223 kg_91_3853
    have h225 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3917 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3913 4 h224 kg_91_3913
    have h226 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3921 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3917 4 h225 kg_91_3917
    have h227 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 3933 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3921 12 h226 kg_91_3921
    have h228 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4053 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 3933 120 h227 kg_91_3933
    have h229 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4164 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4053 111 h228 kg_91_4053
    have h230 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4169 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4164 5 h229 kg_91_4164
    have h231 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4180 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4169 11 h230 kg_91_4169
    have h232 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4251 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4180 71 h231 kg_91_4180
    have h233 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4337 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4251 86 h232 kg_91_4251
    have h234 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4421 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4337 84 h233 kg_91_4337
    have h235 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4437 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4421 16 h234 kg_91_4421
    have h236 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4495 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4437 58 h235 kg_91_4437
    have h237 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4497 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4495 2 h236 kg_91_4495
    have h238 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4501 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4497 4 h237 kg_91_4497
    have h239 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4502 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4501 1 h238 kg_91_4501
    have h240 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4507 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4502 5 h239 kg_91_4502
    have h241 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4511 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4507 4 h240 kg_91_4507
    have h242 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4512 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4511 1 h241 kg_91_4511
    have h243 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4519 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4512 7 h242 kg_91_4512
    have h244 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4640 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4519 121 h243 kg_91_4519
    have h245 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4655 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4640 15 h244 kg_91_4640
    have h246 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4771 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4655 116 h245 kg_91_4655
    have h247 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4780 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4771 9 h246 kg_91_4771
    have h248 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4791 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4780 11 h247 kg_91_4780
    have h249 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4796 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4791 5 h248 kg_91_4791
    have h250 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4797 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4796 1 h249 kg_91_4796
    have h251 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4811 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4797 14 h250 kg_91_4797
    have h252 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4812 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4811 1 h251 kg_91_4811
    have h253 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4844 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4812 32 h252 kg_91_4812
    have h254 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4855 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4844 11 h253 kg_91_4844
    have h255 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4862 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4855 7 h254 kg_91_4855
    have h256 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4863 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4862 1 h255 kg_91_4862
    have h257 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4875 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4863 12 h256 kg_91_4863
    have h258 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4984 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4875 109 h257 kg_91_4875
    have h259 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 4993 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4984 9 h258 kg_91_4984
    have h260 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5110 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 4993 117 h259 kg_91_4993
    have h261 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5124 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5110 14 h260 kg_91_5110
    have h262 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5135 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5124 11 h261 kg_91_5124
    have h263 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5138 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5135 3 h262 kg_91_5135
    have h264 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5170 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5138 32 h263 kg_91_5138
    have h265 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5181 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5170 11 h264 kg_91_5170
    have h266 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5183 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5181 2 h265 kg_91_5181
    have h267 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5184 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5183 1 h266 kg_91_5183
    have h268 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5194 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5184 10 h267 kg_91_5184
    have h269 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5246 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5194 52 h268 kg_91_5194
    have h270 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5307 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5246 61 h269 kg_91_5246
    have h271 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5352 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5307 45 h270 kg_91_5307
    have h272 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5356 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5352 4 h271 kg_91_5352
    have h273 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5369 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5356 13 h272 kg_91_5356
    have h274 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5381 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5369 12 h273 kg_91_5369
    have h275 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5395 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5381 14 h274 kg_91_5381
    have h276 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5412 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5395 17 h275 kg_91_5395
    have h277 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5444 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5412 32 h276 kg_91_5412
    have h278 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5474 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5444 30 h277 kg_91_5444
    have h279 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5475 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5474 1 h278 kg_91_5474
    have h280 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5514 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5475 39 h279 kg_91_5475
    have h281 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5515 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5514 1 h280 kg_91_5514
    have h282 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5538 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5515 23 h281 kg_91_5515
    have h283 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5566 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5538 28 h282 kg_91_5538
    have h284 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5567 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5566 1 h283 kg_91_5566
    have h285 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5597 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5567 30 h284 kg_91_5567
    have h286 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5598 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5597 1 h285 kg_91_5597
    have h287 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5610 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5598 12 h286 kg_91_5598
    have h288 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5611 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5610 1 h287 kg_91_5610
    have h289 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5640 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5611 29 h288 kg_91_5611
    have h290 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5653 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5640 13 h289 kg_91_5640
    have h291 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5654 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5653 1 h290 kg_91_5653
    have h292 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5655 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5654 1 h291 kg_91_5654
    have h293 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5688 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5655 33 h292 kg_91_5655
    have h294 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5689 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5688 1 h293 kg_91_5688
    have h295 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5697 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5689 8 h294 kg_91_5689
    have h296 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5734 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5697 37 h295 kg_91_5697
    have h297 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5735 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5734 1 h296 kg_91_5734
    have h298 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5742 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5735 7 h297 kg_91_5735
    have h299 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5744 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5742 2 h298 kg_91_5742
    have h300 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5772 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5744 28 h299 kg_91_5744
    have h301 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5870 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5772 98 h300 kg_91_5772
    have h302 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5877 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5870 7 h301 kg_91_5870
    have h303 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5878 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5877 1 h302 kg_91_5877
    have h304 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5881 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5878 3 h303 kg_91_5878
    have h305 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5882 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5881 1 h304 kg_91_5881
    have h306 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5887 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5882 5 h305 kg_91_5882
    have h307 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5888 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5887 1 h306 kg_91_5887
    have h308 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5899 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5888 11 h307 kg_91_5888
    have h309 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5919 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5899 20 h308 kg_91_5899
    have h310 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5926 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5919 7 h309 kg_91_5919
    have h311 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5955 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5926 29 h310 kg_91_5926
    have h312 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5968 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5955 13 h311 kg_91_5955
    have h313 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5978 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5968 10 h312 kg_91_5968
    have h314 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 5995 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5978 17 h313 kg_91_5978
    have h315 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6023 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 5995 28 h314 kg_91_5995
    have h316 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6028 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6023 5 h315 kg_91_6023
    have h317 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6043 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6028 15 h316 kg_91_6028
    have h318 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6044 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6043 1 h317 kg_91_6043
    have h319 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6045 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6044 1 h318 kg_91_6044
    have h320 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6047 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6045 2 h319 kg_91_6045
    have h321 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6052 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6047 5 h320 kg_91_6047
    have h322 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6053 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6052 1 h321 kg_91_6052
    have h323 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6056 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6053 3 h322 kg_91_6053
    have h324 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6057 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6056 1 h323 kg_91_6056
    have h325 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6060 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6057 3 h324 kg_91_6057
    have h326 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6068 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6060 8 h325 kg_91_6060
    have h327 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6069 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6068 1 h326 kg_91_6068
    have h328 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6075 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6069 6 h327 kg_91_6069
    have h329 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6076 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6075 1 h328 kg_91_6075
    have h330 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6081 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6076 5 h329 kg_91_6076
    have h331 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6103 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6081 22 h330 kg_91_6081
    have h332 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6129 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6103 26 h331 kg_91_6103
    have h333 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6134 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6129 5 h332 kg_91_6129
    have h334 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6147 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6134 13 h333 kg_91_6134
    have h335 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6154 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6147 7 h334 kg_91_6147
    have h336 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6185 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6154 31 h335 kg_91_6154
    have h337 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6186 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6185 1 h336 kg_91_6185
    have h338 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6187 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6186 1 h337 kg_91_6186
    have h339 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6188 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6187 1 h338 kg_91_6187
    have h340 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6193 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6188 5 h339 kg_91_6188
    have h341 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6194 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6193 1 h340 kg_91_6193
    have h342 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6201 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6194 7 h341 kg_91_6194
    have h343 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6209 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6201 8 h342 kg_91_6201
    have h344 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6232 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6209 23 h343 kg_91_6209
    have h345 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6254 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6232 22 h344 kg_91_6232
    have h346 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6273 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6254 19 h345 kg_91_6254
    have h347 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6274 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6273 1 h346 kg_91_6273
    have h348 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6276 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6274 2 h347 kg_91_6274
    have h349 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6313 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6276 37 h348 kg_91_6276
    have h350 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6330 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6313 17 h349 kg_91_6313
    have h351 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6331 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6330 1 h350 kg_91_6330
    have h352 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6360 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6331 29 h351 kg_91_6331
    have h353 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6380 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6360 20 h352 kg_91_6360
    have h354 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6383 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6380 3 h353 kg_91_6380
    have h355 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6388 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6383 5 h354 kg_91_6383
    have h356 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6409 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6388 21 h355 kg_91_6388
    have h357 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6438 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6409 29 h356 kg_91_6409
    have h358 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6439 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6438 1 h357 kg_91_6438
    have h359 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6454 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6439 15 h358 kg_91_6439
    have h360 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6473 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6454 19 h359 kg_91_6454
    have h361 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6479 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6473 6 h360 kg_91_6473
    have h362 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6480 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6479 1 h361 kg_91_6479
    have h363 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6481 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6480 1 h362 kg_91_6480
    have h364 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6486 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6481 5 h363 kg_91_6481
    have h365 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6504 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6486 18 h364 kg_91_6486
    have h366 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6507 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6504 3 h365 kg_91_6504
    have h367 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 6508 = true := IPChk.allR_join (Pts.glueIB K91.lits KW_91) 0 6507 1 h366 kg_91_6507
    exact h367
  have hlen : K91.lits.length = 6508 := by decide
  intro k h1 h2
  obtain rfl : k = 91 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 91) K91.lits KW_91
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_16 : ∀ k, 92 ≤ k → k < 94 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_92 JW_92 92 2 jr_92
theorem jr6_17 : ∀ k, 94 ≤ k → k < 95 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 420 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 10 = true := kb_94_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 10 14 h0 kb_94_10
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 24 13 h1 kb_94_24
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 37 8 h2 kb_94_37
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 45 61 h3 kb_94_45
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 106 1 h4 kb_94_106
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 107 1 h5 kb_94_107
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 108 27 h6 kb_94_108
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 148 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 135 13 h7 kb_94_135
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 162 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 148 14 h8 kb_94_148
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 162 16 h9 kb_94_162
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 178 15 h10 kb_94_178
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 193 3 h11 kb_94_193
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 260 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 196 64 h12 kb_94_196
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 260 83 h13 kb_94_260
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 377 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 343 34 h14 kb_94_343
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 389 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 377 12 h15 kb_94_377
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 392 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 389 3 h16 kb_94_389
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 397 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 392 5 h17 kb_94_392
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 398 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 397 1 h18 kb_94_397
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 412 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 398 14 h19 kb_94_398
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 420 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K94.lits.getD i 0)) 0 412 8 h20 kb_94_412
    exact h21
  have hg : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 420 = true := by
    have h0 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 10 = true := kg_94_0
    have h1 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 24 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 10 14 h0 kg_94_10
    have h2 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 37 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 24 13 h1 kg_94_24
    have h3 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 45 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 37 8 h2 kg_94_37
    have h4 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 106 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 45 61 h3 kg_94_45
    have h5 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 107 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 106 1 h4 kg_94_106
    have h6 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 108 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 107 1 h5 kg_94_107
    have h7 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 135 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 108 27 h6 kg_94_108
    have h8 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 148 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 135 13 h7 kg_94_135
    have h9 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 162 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 148 14 h8 kg_94_148
    have h10 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 178 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 162 16 h9 kg_94_162
    have h11 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 193 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 178 15 h10 kg_94_178
    have h12 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 196 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 193 3 h11 kg_94_193
    have h13 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 260 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 196 64 h12 kg_94_196
    have h14 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 343 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 260 83 h13 kg_94_260
    have h15 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 377 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 343 34 h14 kg_94_343
    have h16 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 389 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 377 12 h15 kg_94_377
    have h17 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 392 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 389 3 h16 kg_94_389
    have h18 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 397 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 392 5 h17 kg_94_392
    have h19 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 398 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 397 1 h18 kg_94_397
    have h20 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 412 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 398 14 h19 kg_94_398
    have h21 : IPChk.allR (Pts.glueIB K94.lits KW_94) 0 420 = true := IPChk.allR_join (Pts.glueIB K94.lits KW_94) 0 412 8 h20 kg_94_412
    exact h21
  have hlen : K94.lits.length = 420 := by decide
  intro k h1 h2
  obtain rfl : k = 94 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 94) K94.lits KW_94
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_18 : ∀ k, 95 ≤ k → k < 96 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_95 JW_95 95 1 jr_95
theorem jr6_19 : ∀ k, 96 ≤ k → k < 97 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 140 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 2 = true := kb_96_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 15 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 2 13 h0 kb_96_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 15 46 h1 kb_96_15
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 61 20 h2 kb_96_61
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 81 41 h3 kb_96_81
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K96.lits.getD i 0)) 0 122 18 h4 kb_96_122
    exact h5
  have hg : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 140 = true := by
    have h0 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 2 = true := kg_96_0
    have h1 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 15 = true := IPChk.allR_join (Pts.glueIB K96.lits KW_96) 0 2 13 h0 kg_96_2
    have h2 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 61 = true := IPChk.allR_join (Pts.glueIB K96.lits KW_96) 0 15 46 h1 kg_96_15
    have h3 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 81 = true := IPChk.allR_join (Pts.glueIB K96.lits KW_96) 0 61 20 h2 kg_96_61
    have h4 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 122 = true := IPChk.allR_join (Pts.glueIB K96.lits KW_96) 0 81 41 h3 kg_96_81
    have h5 : IPChk.allR (Pts.glueIB K96.lits KW_96) 0 140 = true := IPChk.allR_join (Pts.glueIB K96.lits KW_96) 0 122 18 h4 kg_96_122
    exact h5
  have hlen : K96.lits.length = 140 := by decide
  intro k h1 h2
  obtain rfl : k = 96 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 96) K96.lits KW_96
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_20 : ∀ k, 97 ≤ k → k < 113 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_97 JW_97 97 16 jr_97

theorem grp6_0 : ∀ k, 0 ≤ k → k < 113 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_0
  have a1 := Pts.fa_join a0 jr6_1
  have a2 := Pts.fa_join a1 jr6_2
  have a3 := Pts.fa_join a2 jr6_3
  have a4 := Pts.fa_join a3 jr6_4
  have a5 := Pts.fa_join a4 jr6_5
  have a6 := Pts.fa_join a5 jr6_6
  have a7 := Pts.fa_join a6 jr6_7
  have a8 := Pts.fa_join a7 jr6_8
  have a9 := Pts.fa_join a8 jr6_9
  have a10 := Pts.fa_join a9 jr6_10
  have a11 := Pts.fa_join a10 jr6_11
  have a12 := Pts.fa_join a11 jr6_12
  have a13 := Pts.fa_join a12 jr6_13
  have a14 := Pts.fa_join a13 jr6_14
  have a15 := Pts.fa_join a14 jr6_15
  have a16 := Pts.fa_join a15 jr6_16
  have a17 := Pts.fa_join a16 jr6_17
  have a18 := Pts.fa_join a17 jr6_18
  have a19 := Pts.fa_join a18 jr6_19
  have a20 := Pts.fa_join a19 jr6_20
  exact a20

end B334.E1x.Pts.S707
