import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.JobS
import B334.E1x.Pts.H707.F
import B334.E1x.Pts.S707.J847
import B334.E1x.Pts.S707.J849
import B334.E1x.Pts.S707.J854
import B334.E1x.Pts.S707.J890
import B334.E1x.Pts.S707.J935
import B334.E1x.Pts.S707.J955
import B334.E1x.Pts.S707.J957
import B334.E1x.Pts.S707.J976
import B334.E1x.Pts.S707.J982
import B334.E1x.Pts.S707.J984
import B334.E1x.Pts.S707.K846L
import B334.E1x.Pts.S707.K848L
import B334.E1x.Pts.S707.K853L
import B334.E1x.Pts.S707.K889L
import B334.E1x.Pts.S707.K934L
import B334.E1x.Pts.S707.K954L
import B334.E1x.Pts.S707.K956L
import B334.E1x.Pts.S707.K973L
import B334.E1x.Pts.S707.K974L
import B334.E1x.Pts.S707.K975L
import B334.E1x.Pts.S707.K981L
import B334.E1x.Pts.S707.K983L
import B334.E1x.Pts.S707.K846Q0
import B334.E1x.Pts.S707.K848Q0
import B334.E1x.Pts.S707.K853Q0
import B334.E1x.Pts.S707.K889Q0
import B334.E1x.Pts.S707.K934Q0
import B334.E1x.Pts.S707.K954Q0
import B334.E1x.Pts.S707.K954Q1
import B334.E1x.Pts.S707.K956Q0
import B334.E1x.Pts.S707.K973Q0
import B334.E1x.Pts.S707.K973Q1
import B334.E1x.Pts.S707.K973Q2
import B334.E1x.Pts.S707.K973Q3
import B334.E1x.Pts.S707.K973Q4
import B334.E1x.Pts.S707.K973Q5
import B334.E1x.Pts.S707.K973Q6
import B334.E1x.Pts.S707.K973Q7
import B334.E1x.Pts.S707.K973Q8
import B334.E1x.Pts.S707.K973Q9
import B334.E1x.Pts.S707.K974Q0
import B334.E1x.Pts.S707.K975Q0
import B334.E1x.Pts.S707.K975Q1
import B334.E1x.Pts.S707.K975Q2
import B334.E1x.Pts.S707.K975Q3
import B334.E1x.Pts.S707.K975Q4
import B334.E1x.Pts.S707.K975Q5
import B334.E1x.Pts.S707.K975Q6
import B334.E1x.Pts.S707.K975Q7
import B334.E1x.Pts.S707.K975Q8
import B334.E1x.Pts.S707.K975Q9
import B334.E1x.Pts.S707.K981Q0
import B334.E1x.Pts.S707.K981Q1
import B334.E1x.Pts.S707.K981Q2
import B334.E1x.Pts.S707.K981Q3
import B334.E1x.Pts.S707.K981Q4
import B334.E1x.Pts.S707.K981Q5
import B334.E1x.Pts.S707.K981Q6
import B334.E1x.Pts.S707.K981Q7
import B334.E1x.Pts.S707.K981Q8
import B334.E1x.Pts.S707.K981Q9
import B334.E1x.Pts.S707.K983Q0
import B334.E1x.Pts.S707.K983Q1
import B334.E1x.Pts.S707.K983Q2
import B334.E1x.Pts.S707.K983Q3
import B334.E1x.Pts.S707.K983Q4
import B334.E1x.Pts.S707.K983Q5
import B334.E1x.Pts.S707.K983Q6
import B334.E1x.Pts.S707.K983Q7
import B334.E1x.Pts.S707.K983Q8
import B334.E1x.Pts.S707.K983Q9
import B334.E1x.Pts.S707.K973Q10
import B334.E1x.Pts.S707.K973Q11
import B334.E1x.Pts.S707.K973Q12
import B334.E1x.Pts.S707.K973Q13
import B334.E1x.Pts.S707.K973Q14
import B334.E1x.Pts.S707.K973Q15
import B334.E1x.Pts.S707.K973Q16
import B334.E1x.Pts.S707.K973Q17
import B334.E1x.Pts.S707.K973Q18
import B334.E1x.Pts.S707.K975Q10
import B334.E1x.Pts.S707.K975Q11
import B334.E1x.Pts.S707.K975Q12
import B334.E1x.Pts.S707.K975Q13
import B334.E1x.Pts.S707.K975Q14
import B334.E1x.Pts.S707.K975Q15
import B334.E1x.Pts.S707.K975Q16
import B334.E1x.Pts.S707.K975Q17
import B334.E1x.Pts.S707.K975Q18
import B334.E1x.Pts.S707.K981Q10

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Joined job facts of `S707`, jobs 846 … 984 (stage707_v6): the v5 Fin's job blocks r172 … r199 as
theorems, joined into `grp6_6` -/

namespace B334.E1x.Pts.S707
open B334 B334.E1x B334.E1x.E1PS

theorem jr6_172 : ∀ k, 846 ≤ k → k < 847 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 8 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 1 = true := kb_846_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 1 1 h0 kb_846_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 2 4 h1 kb_846_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K846.lits.getD i 0)) 0 6 2 h2 kb_846_6
    exact h3
  have hg : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 8 = true := by
    have h0 : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 1 = true := kg_846_0
    have h1 : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 2 = true := IPChk.allR_join (Pts.glueIB K846.lits KW_846) 0 1 1 h0 kg_846_1
    have h2 : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 6 = true := IPChk.allR_join (Pts.glueIB K846.lits KW_846) 0 2 4 h1 kg_846_2
    have h3 : IPChk.allR (Pts.glueIB K846.lits KW_846) 0 8 = true := IPChk.allR_join (Pts.glueIB K846.lits KW_846) 0 6 2 h2 kg_846_6
    exact h3
  have hlen : K846.lits.length = 8 := by decide
  intro k h1 h2
  obtain rfl : k = 846 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 846) K846.lits KW_846
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_173 : ∀ k, 847 ≤ k → k < 848 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_847 JW_847 847 1 jr_847
theorem jr6_174 : ∀ k, 848 ≤ k → k < 849 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 0 4 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 0 3 = true := kb_848_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K848.lits.getD i 0)) 0 3 1 h0 kb_848_3
    exact h1
  have hg : IPChk.allR (Pts.glueIB K848.lits KW_848) 0 4 = true := by
    have h0 : IPChk.allR (Pts.glueIB K848.lits KW_848) 0 3 = true := kg_848_0
    have h1 : IPChk.allR (Pts.glueIB K848.lits KW_848) 0 4 = true := IPChk.allR_join (Pts.glueIB K848.lits KW_848) 0 3 1 h0 kg_848_3
    exact h1
  have hlen : K848.lits.length = 4 := by decide
  intro k h1 h2
  obtain rfl : k = 848 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 848) K848.lits KW_848
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_175 : ∀ k, 849 ≤ k → k < 853 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_849 JW_849 849 4 jr_849
theorem jr6_176 : ∀ k, 853 ≤ k → k < 854 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 16 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 1 = true := kb_853_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 1 12 h0 kb_853_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K853.lits.getD i 0)) 0 13 3 h1 kb_853_13
    exact h2
  have hg : IPChk.allR (Pts.glueIB K853.lits KW_853) 0 16 = true := by
    have h0 : IPChk.allR (Pts.glueIB K853.lits KW_853) 0 1 = true := kg_853_0
    have h1 : IPChk.allR (Pts.glueIB K853.lits KW_853) 0 13 = true := IPChk.allR_join (Pts.glueIB K853.lits KW_853) 0 1 12 h0 kg_853_1
    have h2 : IPChk.allR (Pts.glueIB K853.lits KW_853) 0 16 = true := IPChk.allR_join (Pts.glueIB K853.lits KW_853) 0 13 3 h1 kg_853_13
    exact h2
  have hlen : K853.lits.length = 16 := by decide
  intro k h1 h2
  obtain rfl : k = 853 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 853) K853.lits KW_853
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_177 : ∀ k, 854 ≤ k → k < 861 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_854 JW_854 854 7 jr_854
theorem jr6_178 : ∀ k, 861 ≤ k → k < 867 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_854 JW_854 861 6 jr_861
theorem jr6_179 : ∀ k, 867 ≤ k → k < 885 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_854 JW_854 867 18 jr_867
theorem jr6_180 : ∀ k, 885 ≤ k → k < 889 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_854 JW_854 885 4 jr_885
theorem jr6_181 : ∀ k, 889 ≤ k → k < 890 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 12 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 1 = true := kb_889_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 1 5 h0 kb_889_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 11 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 6 5 h1 kb_889_6
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K889.lits.getD i 0)) 0 11 1 h2 kb_889_11
    exact h3
  have hg : IPChk.allR (Pts.glueIB K889.lits KW_889) 0 12 = true := by
    have h0 : IPChk.allR (Pts.glueIB K889.lits KW_889) 0 1 = true := kg_889_0
    have h1 : IPChk.allR (Pts.glueIB K889.lits KW_889) 0 6 = true := IPChk.allR_join (Pts.glueIB K889.lits KW_889) 0 1 5 h0 kg_889_1
    have h2 : IPChk.allR (Pts.glueIB K889.lits KW_889) 0 11 = true := IPChk.allR_join (Pts.glueIB K889.lits KW_889) 0 6 5 h1 kg_889_6
    have h3 : IPChk.allR (Pts.glueIB K889.lits KW_889) 0 12 = true := IPChk.allR_join (Pts.glueIB K889.lits KW_889) 0 11 1 h2 kg_889_11
    exact h3
  have hlen : K889.lits.length = 12 := by decide
  intro k h1 h2
  obtain rfl : k = 889 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 889) K889.lits KW_889
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_182 : ∀ k, 890 ≤ k → k < 900 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_890 JW_890 890 10 jr_890
theorem jr6_183 : ∀ k, 900 ≤ k → k < 906 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_890 JW_890 900 6 jr_900
theorem jr6_184 : ∀ k, 906 ≤ k → k < 919 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_890 JW_890 906 13 jr_906
theorem jr6_185 : ∀ k, 919 ≤ k → k < 934 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_890 JW_890 919 15 jr_919
theorem jr6_186 : ∀ k, 934 ≤ k → k < 935 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 10 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 2 = true := kb_934_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 4 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 2 2 h0 kb_934_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 4 4 h1 kb_934_4
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K934.lits.getD i 0)) 0 8 2 h2 kb_934_8
    exact h3
  have hg : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 10 = true := by
    have h0 : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 2 = true := kg_934_0
    have h1 : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 4 = true := IPChk.allR_join (Pts.glueIB K934.lits KW_934) 0 2 2 h0 kg_934_2
    have h2 : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 8 = true := IPChk.allR_join (Pts.glueIB K934.lits KW_934) 0 4 4 h1 kg_934_4
    have h3 : IPChk.allR (Pts.glueIB K934.lits KW_934) 0 10 = true := IPChk.allR_join (Pts.glueIB K934.lits KW_934) 0 8 2 h2 kg_934_8
    exact h3
  have hlen : K934.lits.length = 10 := by decide
  intro k h1 h2
  obtain rfl : k = 934 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 934) K934.lits KW_934
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_187 : ∀ k, 935 ≤ k → k < 954 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_935 JW_935 935 19 jr_935
theorem jr6_188 : ∀ k, 954 ≤ k → k < 955 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 164 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 4 = true := kb_954_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 4 1 h0 kb_954_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 5 5 h1 kb_954_5
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 10 2 h2 kb_954_10
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 12 2 h3 kb_954_12
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 14 32 h4 kb_954_14
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 46 104 h5 kb_954_46
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 150 1 h6 kb_954_150
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 153 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 151 2 h7 kb_954_151
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 153 3 h8 kb_954_153
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 156 2 h9 kb_954_156
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 158 2 h10 kb_954_158
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 160 1 h11 kb_954_160
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 161 2 h12 kb_954_161
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K954.lits.getD i 0)) 0 163 1 h13 kb_954_163
    exact h14
  have hg : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 164 = true := by
    have h0 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 4 = true := kg_954_0
    have h1 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 5 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 4 1 h0 kg_954_4
    have h2 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 10 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 5 5 h1 kg_954_5
    have h3 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 12 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 10 2 h2 kg_954_10
    have h4 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 14 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 12 2 h3 kg_954_12
    have h5 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 46 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 14 32 h4 kg_954_14
    have h6 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 150 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 46 104 h5 kg_954_46
    have h7 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 151 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 150 1 h6 kg_954_150
    have h8 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 153 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 151 2 h7 kg_954_151
    have h9 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 156 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 153 3 h8 kg_954_153
    have h10 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 158 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 156 2 h9 kg_954_156
    have h11 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 160 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 158 2 h10 kg_954_158
    have h12 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 161 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 160 1 h11 kg_954_160
    have h13 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 163 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 161 2 h12 kg_954_161
    have h14 : IPChk.allR (Pts.glueIB K954.lits KW_954) 0 164 = true := IPChk.allR_join (Pts.glueIB K954.lits KW_954) 0 163 1 h13 kg_954_163
    exact h14
  have hlen : K954.lits.length = 164 := by decide
  intro k h1 h2
  obtain rfl : k = 954 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 954) K954.lits KW_954
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_189 : ∀ k, 955 ≤ k → k < 956 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_955 JW_955 955 1 jr_955
theorem jr6_190 : ∀ k, 956 ≤ k → k < 957 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 70 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 2 = true := kb_956_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 2 6 h0 kb_956_2
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 26 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 8 18 h1 kb_956_8
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 26 12 h2 kb_956_26
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 38 6 h3 kb_956_38
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 66 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 44 22 h4 kb_956_44
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 66 1 h5 kb_956_66
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K956.lits.getD i 0)) 0 67 3 h6 kb_956_67
    exact h7
  have hg : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 70 = true := by
    have h0 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 2 = true := kg_956_0
    have h1 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 8 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 2 6 h0 kg_956_2
    have h2 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 26 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 8 18 h1 kg_956_8
    have h3 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 38 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 26 12 h2 kg_956_26
    have h4 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 44 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 38 6 h3 kg_956_38
    have h5 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 66 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 44 22 h4 kg_956_44
    have h6 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 67 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 66 1 h5 kg_956_66
    have h7 : IPChk.allR (Pts.glueIB K956.lits KW_956) 0 70 = true := IPChk.allR_join (Pts.glueIB K956.lits KW_956) 0 67 3 h6 kg_956_67
    exact h7
  have hlen : K956.lits.length = 70 := by decide
  intro k h1 h2
  obtain rfl : k = 956 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 956) K956.lits KW_956
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_191 : ∀ k, 957 ≤ k → k < 973 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_957 JW_957 957 16 jr_957
theorem jr6_192 : ∀ k, 973 ≤ k → k < 974 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1474 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1 = true := kb_973_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 2 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1 1 h0 kb_973_1
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 2 4 h1 kb_973_2
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 6 1 h2 kb_973_6
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 9 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 7 2 h3 kb_973_7
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 9 4 h4 kb_973_9
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 21 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 13 8 h5 kb_973_13
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 37 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 21 16 h6 kb_973_21
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 37 3 h7 kb_973_37
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 40 2 h8 kb_973_40
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 42 3 h9 kb_973_42
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 49 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 45 4 h10 kb_973_45
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 49 4 h11 kb_973_49
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 53 4 h12 kb_973_53
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 57 2 h13 kb_973_57
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 59 1 h14 kb_973_59
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 69 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 60 9 h15 kb_973_60
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 70 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 69 1 h16 kb_973_69
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 72 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 70 2 h17 kb_973_70
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 73 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 72 1 h18 kb_973_72
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 81 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 73 8 h19 kb_973_73
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 82 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 81 1 h20 kb_973_81
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 83 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 82 1 h21 kb_973_82
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 83 5 h22 kb_973_83
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 89 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 88 1 h23 kb_973_88
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 111 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 89 22 h24 kb_973_89
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 111 13 h25 kb_973_111
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 155 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 124 31 h26 kb_973_124
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 155 1 h27 kb_973_155
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 156 2 h28 kb_973_156
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 160 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 158 2 h29 kb_973_158
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 160 1 h30 kb_973_160
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 161 3 h31 kb_973_161
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 164 1 h32 kb_973_164
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 167 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 165 2 h33 kb_973_165
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 167 3 h34 kb_973_167
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 170 1 h35 kb_973_170
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 172 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 171 1 h36 kb_973_171
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 173 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 172 1 h37 kb_973_172
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 173 1 h38 kb_973_173
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 175 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 174 1 h39 kb_973_174
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 176 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 175 1 h40 kb_973_175
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 176 1 h41 kb_973_176
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 177 1 h42 kb_973_177
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 178 1 h43 kb_973_178
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 179 3 h44 kb_973_179
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 182 5 h45 kb_973_182
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 187 6 h46 kb_973_187
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 196 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 193 3 h47 kb_973_193
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 198 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 196 2 h48 kb_973_196
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 200 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 198 2 h49 kb_973_198
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 200 1 h50 kb_973_200
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 201 1 h51 kb_973_201
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 204 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 202 2 h52 kb_973_202
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 204 1 h53 kb_973_204
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 205 1 h54 kb_973_205
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 207 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 206 1 h55 kb_973_206
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 208 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 207 1 h56 kb_973_207
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 210 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 208 2 h57 kb_973_208
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 211 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 210 1 h58 kb_973_210
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 213 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 211 2 h59 kb_973_211
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 217 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 213 4 h60 kb_973_213
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 246 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 217 29 h61 kb_973_217
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 248 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 246 2 h62 kb_973_246
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 254 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 248 6 h63 kb_973_248
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 256 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 254 2 h64 kb_973_254
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 278 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 256 22 h65 kb_973_256
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 278 60 h66 kb_973_278
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 338 1 h67 kb_973_338
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 340 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 339 1 h68 kb_973_339
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 340 1 h69 kb_973_340
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 341 3 h70 kb_973_341
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 345 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 344 1 h71 kb_973_344
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 348 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 345 3 h72 kb_973_345
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 348 7 h73 kb_973_348
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 405 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 355 50 h74 kb_973_355
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 405 74 h75 kb_973_405
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 508 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 479 29 h76 kb_973_479
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 510 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 508 2 h77 kb_973_508
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 510 6 h78 kb_973_510
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 516 2 h79 kb_973_516
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 540 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 518 22 h80 kb_973_518
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 567 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 540 27 h81 kb_973_540
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 622 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 567 55 h82 kb_973_567
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 720 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 622 98 h83 kb_973_622
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 780 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 720 60 h84 kb_973_720
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 781 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 780 1 h85 kb_973_780
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 782 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 781 1 h86 kb_973_781
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 782 1 h87 kb_973_782
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 784 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 783 1 h88 kb_973_783
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 785 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 784 1 h89 kb_973_784
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 786 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 785 1 h90 kb_973_785
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 787 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 786 1 h91 kb_973_786
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 791 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 787 4 h92 kb_973_787
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 791 29 h93 kb_973_791
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 820 2 h94 kb_973_820
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 822 6 h95 kb_973_822
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 830 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 828 2 h96 kb_973_828
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 852 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 830 22 h97 kb_973_830
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 889 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 852 37 h98 kb_973_852
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 913 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 889 24 h99 kb_973_889
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 914 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 913 1 h100 kb_973_913
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 916 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 914 2 h101 kb_973_914
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 917 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 916 1 h102 kb_973_916
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 918 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 917 1 h103 kb_973_917
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 919 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 918 1 h104 kb_973_918
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 919 1 h105 kb_973_919
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 921 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 920 1 h106 kb_973_920
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 923 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 921 2 h107 kb_973_921
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 931 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 923 8 h108 kb_973_923
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 931 1 h109 kb_973_931
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 932 3 h110 kb_973_932
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 964 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 935 29 h111 kb_973_935
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 966 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 964 2 h112 kb_973_964
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 972 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 966 6 h113 kb_973_966
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 974 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 972 2 h114 kb_973_972
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 996 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 974 22 h115 kb_973_974
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1006 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 996 10 h116 kb_973_996
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1063 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1006 57 h117 kb_973_1006
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1065 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1063 2 h118 kb_973_1063
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1066 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1065 1 h119 kb_973_1065
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1067 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1066 1 h120 kb_973_1066
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1067 1 h121 kb_973_1067
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1068 1 h122 kb_973_1068
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1069 2 h123 kb_973_1069
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1100 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1071 29 h124 kb_973_1071
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1127 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1100 27 h125 kb_973_1100
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1127 6 h126 kb_973_1127
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1133 2 h127 kb_973_1133
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1157 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1135 22 h128 kb_973_1135
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1183 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1157 26 h129 kb_973_1157
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1218 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1183 35 h130 kb_973_1183
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1220 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1218 2 h131 kb_973_1218
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1220 1 h132 kb_973_1220
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1221 2 h133 kb_973_1221
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1228 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1223 5 h134 kb_973_1223
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1230 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1228 2 h135 kb_973_1228
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1230 5 h136 kb_973_1230
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1235 2 h137 kb_973_1235
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1237 1 h138 kb_973_1237
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1244 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1238 6 h139 kb_973_1238
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1250 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1244 6 h140 kb_973_1244
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1259 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1250 9 h141 kb_973_1250
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1267 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1259 8 h142 kb_973_1259
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1269 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1267 2 h143 kb_973_1267
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1284 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1269 15 h144 kb_973_1269
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1286 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1284 2 h145 kb_973_1284
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1305 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1286 19 h146 kb_973_1286
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1310 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1305 5 h147 kb_973_1305
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1310 3 h148 kb_973_1310
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1334 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1313 21 h149 kb_973_1313
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1336 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1334 2 h150 kb_973_1334
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1337 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1336 1 h151 kb_973_1336
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1338 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1337 1 h152 kb_973_1337
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1339 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1338 1 h153 kb_973_1338
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1341 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1339 2 h154 kb_973_1339
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1343 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1341 2 h155 kb_973_1341
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1343 1 h156 kb_973_1343
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1346 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1344 2 h157 kb_973_1344
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1349 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1346 3 h158 kb_973_1346
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1349 1 h159 kb_973_1349
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1350 1 h160 kb_973_1350
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1351 1 h161 kb_973_1351
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1352 1 h162 kb_973_1352
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1355 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1353 2 h163 kb_973_1353
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1356 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1355 1 h164 kb_973_1355
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1357 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1356 1 h165 kb_973_1356
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1357 2 h166 kb_973_1357
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1359 2 h167 kb_973_1359
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1364 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1361 3 h168 kb_973_1361
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1365 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1364 1 h169 kb_973_1364
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1366 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1365 1 h170 kb_973_1365
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1368 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1366 2 h171 kb_973_1366
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1370 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1368 2 h172 kb_973_1368
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1371 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1370 1 h173 kb_973_1370
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1372 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1371 1 h174 kb_973_1371
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1373 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1372 1 h175 kb_973_1372
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1373 1 h176 kb_973_1373
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1374 1 h177 kb_973_1374
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1375 1 h178 kb_973_1375
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1376 2 h179 kb_973_1376
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1378 4 h180 kb_973_1378
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1382 2 h181 kb_973_1382
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1387 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1384 3 h182 kb_973_1384
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1396 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1387 9 h183 kb_973_1387
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1402 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1396 6 h184 kb_973_1396
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1408 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1402 6 h185 kb_973_1402
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1410 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1408 2 h186 kb_973_1408
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1439 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1410 29 h187 kb_973_1410
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1443 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1439 4 h188 kb_973_1439
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1460 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1443 17 h189 kb_973_1443
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1462 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1460 2 h190 kb_973_1460
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1474 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 0 1462 12 h191 kb_973_1462
    exact h192
  have hg : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1474 = true := by
    have h0 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1 = true := kg_973_0
    have h1 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 2 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1 1 h0 kg_973_1
    have h2 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 6 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 2 4 h1 kg_973_2
    have h3 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 7 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 6 1 h2 kg_973_6
    have h4 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 9 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 7 2 h3 kg_973_7
    have h5 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 13 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 9 4 h4 kg_973_9
    have h6 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 21 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 13 8 h5 kg_973_13
    have h7 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 37 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 21 16 h6 kg_973_21
    have h8 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 40 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 37 3 h7 kg_973_37
    have h9 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 42 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 40 2 h8 kg_973_40
    have h10 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 45 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 42 3 h9 kg_973_42
    have h11 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 49 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 45 4 h10 kg_973_45
    have h12 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 53 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 49 4 h11 kg_973_49
    have h13 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 57 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 53 4 h12 kg_973_53
    have h14 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 59 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 57 2 h13 kg_973_57
    have h15 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 60 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 59 1 h14 kg_973_59
    have h16 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 69 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 60 9 h15 kg_973_60
    have h17 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 70 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 69 1 h16 kg_973_69
    have h18 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 72 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 70 2 h17 kg_973_70
    have h19 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 73 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 72 1 h18 kg_973_72
    have h20 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 81 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 73 8 h19 kg_973_73
    have h21 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 82 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 81 1 h20 kg_973_81
    have h22 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 83 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 82 1 h21 kg_973_82
    have h23 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 88 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 83 5 h22 kg_973_83
    have h24 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 89 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 88 1 h23 kg_973_88
    have h25 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 111 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 89 22 h24 kg_973_89
    have h26 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 124 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 111 13 h25 kg_973_111
    have h27 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 155 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 124 31 h26 kg_973_124
    have h28 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 156 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 155 1 h27 kg_973_155
    have h29 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 158 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 156 2 h28 kg_973_156
    have h30 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 160 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 158 2 h29 kg_973_158
    have h31 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 161 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 160 1 h30 kg_973_160
    have h32 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 164 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 161 3 h31 kg_973_161
    have h33 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 165 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 164 1 h32 kg_973_164
    have h34 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 167 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 165 2 h33 kg_973_165
    have h35 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 170 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 167 3 h34 kg_973_167
    have h36 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 171 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 170 1 h35 kg_973_170
    have h37 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 172 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 171 1 h36 kg_973_171
    have h38 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 173 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 172 1 h37 kg_973_172
    have h39 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 174 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 173 1 h38 kg_973_173
    have h40 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 175 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 174 1 h39 kg_973_174
    have h41 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 176 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 175 1 h40 kg_973_175
    have h42 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 177 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 176 1 h41 kg_973_176
    have h43 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 178 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 177 1 h42 kg_973_177
    have h44 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 179 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 178 1 h43 kg_973_178
    have h45 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 182 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 179 3 h44 kg_973_179
    have h46 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 187 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 182 5 h45 kg_973_182
    have h47 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 193 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 187 6 h46 kg_973_187
    have h48 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 196 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 193 3 h47 kg_973_193
    have h49 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 198 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 196 2 h48 kg_973_196
    have h50 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 200 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 198 2 h49 kg_973_198
    have h51 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 201 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 200 1 h50 kg_973_200
    have h52 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 202 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 201 1 h51 kg_973_201
    have h53 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 204 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 202 2 h52 kg_973_202
    have h54 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 205 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 204 1 h53 kg_973_204
    have h55 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 206 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 205 1 h54 kg_973_205
    have h56 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 207 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 206 1 h55 kg_973_206
    have h57 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 208 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 207 1 h56 kg_973_207
    have h58 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 210 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 208 2 h57 kg_973_208
    have h59 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 211 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 210 1 h58 kg_973_210
    have h60 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 213 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 211 2 h59 kg_973_211
    have h61 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 217 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 213 4 h60 kg_973_213
    have h62 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 246 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 217 29 h61 kg_973_217
    have h63 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 248 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 246 2 h62 kg_973_246
    have h64 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 254 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 248 6 h63 kg_973_248
    have h65 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 256 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 254 2 h64 kg_973_254
    have h66 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 278 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 256 22 h65 kg_973_256
    have h67 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 338 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 278 60 h66 kg_973_278
    have h68 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 339 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 338 1 h67 kg_973_338
    have h69 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 340 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 339 1 h68 kg_973_339
    have h70 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 341 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 340 1 h69 kg_973_340
    have h71 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 344 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 341 3 h70 kg_973_341
    have h72 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 345 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 344 1 h71 kg_973_344
    have h73 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 348 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 345 3 h72 kg_973_345
    have h74 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 355 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 348 7 h73 kg_973_348
    have h75 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 405 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 355 50 h74 kg_973_355
    have h76 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 479 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 405 74 h75 kg_973_405
    have h77 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 508 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 479 29 h76 kg_973_479
    have h78 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 510 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 508 2 h77 kg_973_508
    have h79 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 516 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 510 6 h78 kg_973_510
    have h80 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 518 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 516 2 h79 kg_973_516
    have h81 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 540 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 518 22 h80 kg_973_518
    have h82 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 567 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 540 27 h81 kg_973_540
    have h83 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 622 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 567 55 h82 kg_973_567
    have h84 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 720 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 622 98 h83 kg_973_622
    have h85 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 780 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 720 60 h84 kg_973_720
    have h86 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 781 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 780 1 h85 kg_973_780
    have h87 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 782 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 781 1 h86 kg_973_781
    have h88 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 783 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 782 1 h87 kg_973_782
    have h89 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 784 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 783 1 h88 kg_973_783
    have h90 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 785 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 784 1 h89 kg_973_784
    have h91 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 786 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 785 1 h90 kg_973_785
    have h92 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 787 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 786 1 h91 kg_973_786
    have h93 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 791 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 787 4 h92 kg_973_787
    have h94 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 820 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 791 29 h93 kg_973_791
    have h95 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 822 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 820 2 h94 kg_973_820
    have h96 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 828 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 822 6 h95 kg_973_822
    have h97 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 830 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 828 2 h96 kg_973_828
    have h98 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 852 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 830 22 h97 kg_973_830
    have h99 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 889 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 852 37 h98 kg_973_852
    have h100 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 913 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 889 24 h99 kg_973_889
    have h101 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 914 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 913 1 h100 kg_973_913
    have h102 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 916 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 914 2 h101 kg_973_914
    have h103 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 917 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 916 1 h102 kg_973_916
    have h104 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 918 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 917 1 h103 kg_973_917
    have h105 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 919 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 918 1 h104 kg_973_918
    have h106 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 920 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 919 1 h105 kg_973_919
    have h107 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 921 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 920 1 h106 kg_973_920
    have h108 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 923 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 921 2 h107 kg_973_921
    have h109 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 931 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 923 8 h108 kg_973_923
    have h110 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 932 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 931 1 h109 kg_973_931
    have h111 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 935 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 932 3 h110 kg_973_932
    have h112 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 964 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 935 29 h111 kg_973_935
    have h113 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 966 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 964 2 h112 kg_973_964
    have h114 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 972 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 966 6 h113 kg_973_966
    have h115 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 974 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 972 2 h114 kg_973_972
    have h116 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 996 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 974 22 h115 kg_973_974
    have h117 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1006 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 996 10 h116 kg_973_996
    have h118 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1063 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1006 57 h117 kg_973_1006
    have h119 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1065 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1063 2 h118 kg_973_1063
    have h120 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1066 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1065 1 h119 kg_973_1065
    have h121 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1067 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1066 1 h120 kg_973_1066
    have h122 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1068 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1067 1 h121 kg_973_1067
    have h123 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1069 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1068 1 h122 kg_973_1068
    have h124 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1071 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1069 2 h123 kg_973_1069
    have h125 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1100 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1071 29 h124 kg_973_1071
    have h126 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1127 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1100 27 h125 kg_973_1100
    have h127 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1133 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1127 6 h126 kg_973_1127
    have h128 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1135 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1133 2 h127 kg_973_1133
    have h129 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1157 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1135 22 h128 kg_973_1135
    have h130 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1183 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1157 26 h129 kg_973_1157
    have h131 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1218 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1183 35 h130 kg_973_1183
    have h132 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1220 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1218 2 h131 kg_973_1218
    have h133 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1221 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1220 1 h132 kg_973_1220
    have h134 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1223 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1221 2 h133 kg_973_1221
    have h135 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1228 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1223 5 h134 kg_973_1223
    have h136 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1230 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1228 2 h135 kg_973_1228
    have h137 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1235 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1230 5 h136 kg_973_1230
    have h138 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1237 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1235 2 h137 kg_973_1235
    have h139 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1238 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1237 1 h138 kg_973_1237
    have h140 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1244 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1238 6 h139 kg_973_1238
    have h141 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1250 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1244 6 h140 kg_973_1244
    have h142 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1259 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1250 9 h141 kg_973_1250
    have h143 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1267 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1259 8 h142 kg_973_1259
    have h144 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1269 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1267 2 h143 kg_973_1267
    have h145 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1284 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1269 15 h144 kg_973_1269
    have h146 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1286 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1284 2 h145 kg_973_1284
    have h147 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1305 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1286 19 h146 kg_973_1286
    have h148 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1310 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1305 5 h147 kg_973_1305
    have h149 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1313 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1310 3 h148 kg_973_1310
    have h150 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1334 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1313 21 h149 kg_973_1313
    have h151 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1336 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1334 2 h150 kg_973_1334
    have h152 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1337 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1336 1 h151 kg_973_1336
    have h153 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1338 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1337 1 h152 kg_973_1337
    have h154 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1339 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1338 1 h153 kg_973_1338
    have h155 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1341 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1339 2 h154 kg_973_1339
    have h156 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1343 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1341 2 h155 kg_973_1341
    have h157 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1344 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1343 1 h156 kg_973_1343
    have h158 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1346 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1344 2 h157 kg_973_1344
    have h159 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1349 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1346 3 h158 kg_973_1346
    have h160 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1350 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1349 1 h159 kg_973_1349
    have h161 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1351 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1350 1 h160 kg_973_1350
    have h162 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1352 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1351 1 h161 kg_973_1351
    have h163 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1353 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1352 1 h162 kg_973_1352
    have h164 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1355 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1353 2 h163 kg_973_1353
    have h165 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1356 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1355 1 h164 kg_973_1355
    have h166 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1357 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1356 1 h165 kg_973_1356
    have h167 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1359 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1357 2 h166 kg_973_1357
    have h168 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1361 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1359 2 h167 kg_973_1359
    have h169 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1364 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1361 3 h168 kg_973_1361
    have h170 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1365 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1364 1 h169 kg_973_1364
    have h171 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1366 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1365 1 h170 kg_973_1365
    have h172 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1368 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1366 2 h171 kg_973_1366
    have h173 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1370 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1368 2 h172 kg_973_1368
    have h174 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1371 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1370 1 h173 kg_973_1370
    have h175 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1372 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1371 1 h174 kg_973_1371
    have h176 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1373 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1372 1 h175 kg_973_1372
    have h177 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1374 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1373 1 h176 kg_973_1373
    have h178 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1375 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1374 1 h177 kg_973_1374
    have h179 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1376 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1375 1 h178 kg_973_1375
    have h180 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1378 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1376 2 h179 kg_973_1376
    have h181 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1382 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1378 4 h180 kg_973_1378
    have h182 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1384 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1382 2 h181 kg_973_1382
    have h183 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1387 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1384 3 h182 kg_973_1384
    have h184 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1396 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1387 9 h183 kg_973_1387
    have h185 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1402 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1396 6 h184 kg_973_1396
    have h186 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1408 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1402 6 h185 kg_973_1402
    have h187 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1410 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1408 2 h186 kg_973_1408
    have h188 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1439 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1410 29 h187 kg_973_1410
    have h189 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1443 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1439 4 h188 kg_973_1439
    have h190 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1460 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1443 17 h189 kg_973_1443
    have h191 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1462 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1460 2 h190 kg_973_1460
    have h192 : IPChk.allR (Pts.glueIB K973.lits KW_973) 0 1474 = true := IPChk.allR_join (Pts.glueIB K973.lits KW_973) 0 1462 12 h191 kg_973_1462
    exact h192
  have hlen : K973.lits.length = 1474 := by decide
  intro k h1 h2
  obtain rfl : k = 973 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 973) K973.lits KW_973
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_193 : ∀ k, 974 ≤ k → k < 975 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 6 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 4 = true := kb_974_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 4 1 h0 kb_974_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 6 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K974.lits.getD i 0)) 0 5 1 h1 kb_974_5
    exact h2
  have hg : IPChk.allR (Pts.glueIB K974.lits KW_974) 0 6 = true := by
    have h0 : IPChk.allR (Pts.glueIB K974.lits KW_974) 0 4 = true := kg_974_0
    have h1 : IPChk.allR (Pts.glueIB K974.lits KW_974) 0 5 = true := IPChk.allR_join (Pts.glueIB K974.lits KW_974) 0 4 1 h0 kg_974_4
    have h2 : IPChk.allR (Pts.glueIB K974.lits KW_974) 0 6 = true := IPChk.allR_join (Pts.glueIB K974.lits KW_974) 0 5 1 h1 kg_974_5
    exact h2
  have hlen : K974.lits.length = 6 := by decide
  intro k h1 h2
  obtain rfl : k = 974 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 974) K974.lits KW_974
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_194 : ∀ k, 975 ≤ k → k < 976 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1206 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 4 = true := kb_975_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 4 3 h0 kb_975_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 7 6 h1 kb_975_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 16 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 13 3 h2 kb_975_13
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 17 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 16 1 h3 kb_975_16
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 30 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 17 13 h4 kb_975_17
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 30 2 h5 kb_975_30
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 32 1 h6 kb_975_32
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 33 6 h7 kb_975_33
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 40 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 39 1 h8 kb_975_39
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 40 1 h9 kb_975_40
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 41 2 h10 kb_975_41
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 43 1 h11 kb_975_43
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 44 1 h12 kb_975_44
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 45 2 h13 kb_975_45
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 48 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 47 1 h14 kb_975_47
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 48 5 h15 kb_975_48
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 55 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 53 2 h16 kb_975_53
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 56 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 55 1 h17 kb_975_55
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 57 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 56 1 h18 kb_975_56
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 57 6 h19 kb_975_57
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 64 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 63 1 h20 kb_975_63
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 68 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 64 4 h21 kb_975_64
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 88 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 68 20 h22 kb_975_68
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 99 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 88 11 h23 kb_975_88
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 99 6 h24 kb_975_99
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 105 2 h25 kb_975_105
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 107 61 h26 kb_975_107
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 209 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 168 41 h27 kb_975_168
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 238 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 209 29 h28 kb_975_209
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 239 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 238 1 h29 kb_975_238
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 241 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 239 2 h30 kb_975_239
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 243 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 241 2 h31 kb_975_241
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 272 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 243 29 h32 kb_975_243
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 274 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 272 2 h33 kb_975_272
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 281 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 274 7 h34 kb_975_274
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 331 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 281 50 h35 kb_975_281
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 375 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 331 44 h36 kb_975_331
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 376 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 375 1 h37 kb_975_375
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 378 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 376 2 h38 kb_975_376
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 379 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 378 1 h39 kb_975_378
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 381 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 379 2 h40 kb_975_379
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 382 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 381 1 h41 kb_975_381
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 384 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 382 2 h42 kb_975_382
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 413 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 384 29 h43 kb_975_384
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 415 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 413 2 h44 kb_975_413
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 421 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 415 6 h45 kb_975_415
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 423 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 421 2 h46 kb_975_421
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 472 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 423 49 h47 kb_975_423
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 511 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 472 39 h48 kb_975_472
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 512 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 511 1 h49 kb_975_511
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 514 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 512 2 h50 kb_975_512
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 516 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 514 2 h51 kb_975_514
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 517 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 516 1 h52 kb_975_516
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 518 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 517 1 h53 kb_975_517
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 520 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 518 2 h54 kb_975_518
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 549 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 520 29 h55 kb_975_520
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 551 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 549 2 h56 kb_975_549
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 557 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 551 6 h57 kb_975_551
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 557 2 h58 kb_975_557
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 596 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 559 37 h59 kb_975_559
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 652 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 596 56 h60 kb_975_596
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 653 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 652 1 h61 kb_975_652
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 654 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 653 1 h62 kb_975_653
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 654 38 h63 kb_975_654
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 692 1 h64 kb_975_692
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 695 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 693 2 h65 kb_975_693
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 695 27 h66 kb_975_695
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 726 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 722 4 h67 kb_975_722
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 726 7 h68 kb_975_726
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 778 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 733 45 h69 kb_975_733
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 834 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 778 56 h70 kb_975_778
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 841 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 834 7 h71 kb_975_834
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 881 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 841 40 h72 kb_975_841
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 910 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 881 29 h73 kb_975_881
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 912 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 910 2 h74 kb_975_910
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 918 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 912 6 h75 kb_975_912
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 920 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 918 2 h76 kb_975_918
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 949 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 920 29 h77 kb_975_920
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1021 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 949 72 h78 kb_975_949
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1022 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1021 1 h79 kb_975_1021
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1029 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1022 7 h80 kb_975_1022
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1032 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1029 3 h81 kb_975_1029
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1035 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1032 3 h82 kb_975_1032
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1042 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1035 7 h83 kb_975_1035
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1043 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1042 1 h84 kb_975_1042
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1045 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1043 2 h85 kb_975_1043
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1046 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1045 1 h86 kb_975_1045
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1048 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1046 2 h87 kb_975_1046
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1050 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1048 2 h88 kb_975_1048
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1052 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1050 2 h89 kb_975_1050
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1053 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1052 1 h90 kb_975_1052
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1054 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1053 1 h91 kb_975_1053
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1055 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1054 1 h92 kb_975_1054
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1057 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1055 2 h93 kb_975_1055
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1058 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1057 1 h94 kb_975_1057
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1059 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1058 1 h95 kb_975_1058
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1060 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1059 1 h96 kb_975_1059
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1061 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1060 1 h97 kb_975_1060
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1062 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1061 1 h98 kb_975_1061
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1064 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1062 2 h99 kb_975_1062
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1067 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1064 3 h100 kb_975_1064
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1068 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1067 1 h101 kb_975_1067
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1069 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1068 1 h102 kb_975_1068
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1070 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1069 1 h103 kb_975_1069
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1071 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1070 1 h104 kb_975_1070
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1072 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1071 1 h105 kb_975_1071
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1075 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1072 3 h106 kb_975_1072
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1077 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1075 2 h107 kb_975_1075
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1078 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1077 1 h108 kb_975_1077
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1079 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1078 1 h109 kb_975_1078
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1080 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1079 1 h110 kb_975_1079
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1081 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1080 1 h111 kb_975_1080
    have h113 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1082 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1081 1 h112 kb_975_1081
    have h114 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1084 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1082 2 h113 kb_975_1082
    have h115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1086 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1084 2 h114 kb_975_1084
    have h116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1088 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1086 2 h115 kb_975_1086
    have h117 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1089 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1088 1 h116 kb_975_1088
    have h118 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1090 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1089 1 h117 kb_975_1089
    have h119 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1092 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1090 2 h118 kb_975_1090
    have h120 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1094 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1092 2 h119 kb_975_1092
    have h121 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1095 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1094 1 h120 kb_975_1094
    have h122 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1097 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1095 2 h121 kb_975_1095
    have h123 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1099 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1097 2 h122 kb_975_1097
    have h124 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1101 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1099 2 h123 kb_975_1099
    have h125 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1103 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1101 2 h124 kb_975_1101
    have h126 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1104 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1103 1 h125 kb_975_1103
    have h127 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1105 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1104 1 h126 kb_975_1104
    have h128 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1106 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1105 1 h127 kb_975_1105
    have h129 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1108 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1106 2 h128 kb_975_1106
    have h130 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1109 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1108 1 h129 kb_975_1108
    have h131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1110 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1109 1 h130 kb_975_1109
    have h132 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1112 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1110 2 h131 kb_975_1110
    have h133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1113 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1112 1 h132 kb_975_1112
    have h134 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1115 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1113 2 h133 kb_975_1113
    have h135 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1117 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1115 2 h134 kb_975_1115
    have h136 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1118 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1117 1 h135 kb_975_1117
    have h137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1120 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1118 2 h136 kb_975_1118
    have h138 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1123 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1120 3 h137 kb_975_1120
    have h139 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1124 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1123 1 h138 kb_975_1123
    have h140 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1125 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1124 1 h139 kb_975_1124
    have h141 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1126 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1125 1 h140 kb_975_1125
    have h142 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1128 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1126 2 h141 kb_975_1126
    have h143 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1129 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1128 1 h142 kb_975_1128
    have h144 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1130 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1129 1 h143 kb_975_1129
    have h145 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1131 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1130 1 h144 kb_975_1130
    have h146 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1132 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1131 1 h145 kb_975_1131
    have h147 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1133 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1132 1 h146 kb_975_1132
    have h148 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1134 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1133 1 h147 kb_975_1133
    have h149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1135 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1134 1 h148 kb_975_1134
    have h150 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1137 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1135 2 h149 kb_975_1135
    have h151 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1139 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1137 2 h150 kb_975_1137
    have h152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1141 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1139 2 h151 kb_975_1139
    have h153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1142 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1141 1 h152 kb_975_1141
    have h154 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1143 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1142 1 h153 kb_975_1142
    have h155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1144 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1143 1 h154 kb_975_1143
    have h156 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1145 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1144 1 h155 kb_975_1144
    have h157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1147 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1145 2 h156 kb_975_1145
    have h158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1150 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1147 3 h157 kb_975_1147
    have h159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1151 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1150 1 h158 kb_975_1150
    have h160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1152 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1151 1 h159 kb_975_1151
    have h161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1154 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1152 2 h160 kb_975_1152
    have h162 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1156 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1154 2 h161 kb_975_1154
    have h163 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1158 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1156 2 h162 kb_975_1156
    have h164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1159 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1158 1 h163 kb_975_1158
    have h165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1161 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1159 2 h164 kb_975_1159
    have h166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1163 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1161 2 h165 kb_975_1161
    have h167 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1164 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1163 1 h166 kb_975_1163
    have h168 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1165 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1164 1 h167 kb_975_1164
    have h169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1166 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1165 1 h168 kb_975_1165
    have h170 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1168 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1166 2 h169 kb_975_1166
    have h171 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1170 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1168 2 h170 kb_975_1168
    have h172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1171 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1170 1 h171 kb_975_1170
    have h173 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1174 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1171 3 h172 kb_975_1171
    have h174 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1177 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1174 3 h173 kb_975_1174
    have h175 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1178 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1177 1 h174 kb_975_1177
    have h176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1179 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1178 1 h175 kb_975_1178
    have h177 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1182 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1179 3 h176 kb_975_1179
    have h178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1184 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1182 2 h177 kb_975_1182
    have h179 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1186 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1184 2 h178 kb_975_1184
    have h180 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1186 1 h179 kb_975_1186
    have h181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1187 1 h180 kb_975_1187
    have h182 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1188 1 h181 kb_975_1188
    have h183 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1189 1 h182 kb_975_1189
    have h184 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1192 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1190 2 h183 kb_975_1190
    have h185 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1192 2 h184 kb_975_1192
    have h186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1194 3 h185 kb_975_1194
    have h187 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1199 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1197 2 h186 kb_975_1197
    have h188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1201 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1199 2 h187 kb_975_1199
    have h189 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1202 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1201 1 h188 kb_975_1201
    have h190 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1203 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1202 1 h189 kb_975_1202
    have h191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1205 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1203 2 h190 kb_975_1203
    have h192 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1206 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K975.lits.getD i 0)) 0 1205 1 h191 kb_975_1205
    exact h192
  have hg : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1206 = true := by
    have h0 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 4 = true := kg_975_0
    have h1 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 7 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 4 3 h0 kg_975_4
    have h2 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 13 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 7 6 h1 kg_975_7
    have h3 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 16 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 13 3 h2 kg_975_13
    have h4 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 17 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 16 1 h3 kg_975_16
    have h5 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 30 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 17 13 h4 kg_975_17
    have h6 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 32 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 30 2 h5 kg_975_30
    have h7 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 33 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 32 1 h6 kg_975_32
    have h8 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 39 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 33 6 h7 kg_975_33
    have h9 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 40 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 39 1 h8 kg_975_39
    have h10 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 41 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 40 1 h9 kg_975_40
    have h11 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 43 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 41 2 h10 kg_975_41
    have h12 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 44 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 43 1 h11 kg_975_43
    have h13 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 45 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 44 1 h12 kg_975_44
    have h14 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 47 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 45 2 h13 kg_975_45
    have h15 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 48 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 47 1 h14 kg_975_47
    have h16 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 53 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 48 5 h15 kg_975_48
    have h17 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 55 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 53 2 h16 kg_975_53
    have h18 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 56 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 55 1 h17 kg_975_55
    have h19 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 57 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 56 1 h18 kg_975_56
    have h20 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 63 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 57 6 h19 kg_975_57
    have h21 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 64 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 63 1 h20 kg_975_63
    have h22 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 68 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 64 4 h21 kg_975_64
    have h23 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 88 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 68 20 h22 kg_975_68
    have h24 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 99 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 88 11 h23 kg_975_88
    have h25 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 105 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 99 6 h24 kg_975_99
    have h26 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 107 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 105 2 h25 kg_975_105
    have h27 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 168 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 107 61 h26 kg_975_107
    have h28 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 209 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 168 41 h27 kg_975_168
    have h29 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 238 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 209 29 h28 kg_975_209
    have h30 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 239 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 238 1 h29 kg_975_238
    have h31 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 241 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 239 2 h30 kg_975_239
    have h32 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 243 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 241 2 h31 kg_975_241
    have h33 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 272 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 243 29 h32 kg_975_243
    have h34 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 274 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 272 2 h33 kg_975_272
    have h35 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 281 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 274 7 h34 kg_975_274
    have h36 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 331 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 281 50 h35 kg_975_281
    have h37 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 375 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 331 44 h36 kg_975_331
    have h38 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 376 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 375 1 h37 kg_975_375
    have h39 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 378 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 376 2 h38 kg_975_376
    have h40 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 379 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 378 1 h39 kg_975_378
    have h41 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 381 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 379 2 h40 kg_975_379
    have h42 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 382 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 381 1 h41 kg_975_381
    have h43 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 384 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 382 2 h42 kg_975_382
    have h44 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 413 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 384 29 h43 kg_975_384
    have h45 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 415 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 413 2 h44 kg_975_413
    have h46 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 421 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 415 6 h45 kg_975_415
    have h47 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 423 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 421 2 h46 kg_975_421
    have h48 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 472 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 423 49 h47 kg_975_423
    have h49 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 511 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 472 39 h48 kg_975_472
    have h50 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 512 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 511 1 h49 kg_975_511
    have h51 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 514 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 512 2 h50 kg_975_512
    have h52 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 516 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 514 2 h51 kg_975_514
    have h53 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 517 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 516 1 h52 kg_975_516
    have h54 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 518 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 517 1 h53 kg_975_517
    have h55 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 520 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 518 2 h54 kg_975_518
    have h56 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 549 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 520 29 h55 kg_975_520
    have h57 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 551 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 549 2 h56 kg_975_549
    have h58 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 557 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 551 6 h57 kg_975_551
    have h59 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 559 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 557 2 h58 kg_975_557
    have h60 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 596 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 559 37 h59 kg_975_559
    have h61 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 652 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 596 56 h60 kg_975_596
    have h62 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 653 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 652 1 h61 kg_975_652
    have h63 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 654 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 653 1 h62 kg_975_653
    have h64 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 692 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 654 38 h63 kg_975_654
    have h65 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 693 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 692 1 h64 kg_975_692
    have h66 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 695 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 693 2 h65 kg_975_693
    have h67 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 722 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 695 27 h66 kg_975_695
    have h68 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 726 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 722 4 h67 kg_975_722
    have h69 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 733 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 726 7 h68 kg_975_726
    have h70 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 778 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 733 45 h69 kg_975_733
    have h71 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 834 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 778 56 h70 kg_975_778
    have h72 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 841 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 834 7 h71 kg_975_834
    have h73 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 881 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 841 40 h72 kg_975_841
    have h74 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 910 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 881 29 h73 kg_975_881
    have h75 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 912 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 910 2 h74 kg_975_910
    have h76 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 918 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 912 6 h75 kg_975_912
    have h77 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 920 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 918 2 h76 kg_975_918
    have h78 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 949 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 920 29 h77 kg_975_920
    have h79 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1021 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 949 72 h78 kg_975_949
    have h80 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1022 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1021 1 h79 kg_975_1021
    have h81 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1029 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1022 7 h80 kg_975_1022
    have h82 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1032 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1029 3 h81 kg_975_1029
    have h83 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1035 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1032 3 h82 kg_975_1032
    have h84 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1042 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1035 7 h83 kg_975_1035
    have h85 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1043 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1042 1 h84 kg_975_1042
    have h86 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1045 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1043 2 h85 kg_975_1043
    have h87 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1046 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1045 1 h86 kg_975_1045
    have h88 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1048 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1046 2 h87 kg_975_1046
    have h89 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1050 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1048 2 h88 kg_975_1048
    have h90 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1052 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1050 2 h89 kg_975_1050
    have h91 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1053 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1052 1 h90 kg_975_1052
    have h92 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1054 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1053 1 h91 kg_975_1053
    have h93 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1055 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1054 1 h92 kg_975_1054
    have h94 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1057 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1055 2 h93 kg_975_1055
    have h95 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1058 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1057 1 h94 kg_975_1057
    have h96 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1059 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1058 1 h95 kg_975_1058
    have h97 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1060 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1059 1 h96 kg_975_1059
    have h98 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1061 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1060 1 h97 kg_975_1060
    have h99 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1062 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1061 1 h98 kg_975_1061
    have h100 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1064 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1062 2 h99 kg_975_1062
    have h101 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1067 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1064 3 h100 kg_975_1064
    have h102 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1068 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1067 1 h101 kg_975_1067
    have h103 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1069 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1068 1 h102 kg_975_1068
    have h104 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1070 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1069 1 h103 kg_975_1069
    have h105 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1071 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1070 1 h104 kg_975_1070
    have h106 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1072 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1071 1 h105 kg_975_1071
    have h107 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1075 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1072 3 h106 kg_975_1072
    have h108 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1077 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1075 2 h107 kg_975_1075
    have h109 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1078 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1077 1 h108 kg_975_1077
    have h110 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1079 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1078 1 h109 kg_975_1078
    have h111 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1080 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1079 1 h110 kg_975_1079
    have h112 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1081 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1080 1 h111 kg_975_1080
    have h113 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1082 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1081 1 h112 kg_975_1081
    have h114 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1084 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1082 2 h113 kg_975_1082
    have h115 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1086 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1084 2 h114 kg_975_1084
    have h116 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1088 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1086 2 h115 kg_975_1086
    have h117 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1089 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1088 1 h116 kg_975_1088
    have h118 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1090 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1089 1 h117 kg_975_1089
    have h119 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1092 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1090 2 h118 kg_975_1090
    have h120 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1094 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1092 2 h119 kg_975_1092
    have h121 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1095 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1094 1 h120 kg_975_1094
    have h122 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1097 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1095 2 h121 kg_975_1095
    have h123 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1099 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1097 2 h122 kg_975_1097
    have h124 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1101 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1099 2 h123 kg_975_1099
    have h125 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1103 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1101 2 h124 kg_975_1101
    have h126 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1104 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1103 1 h125 kg_975_1103
    have h127 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1105 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1104 1 h126 kg_975_1104
    have h128 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1106 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1105 1 h127 kg_975_1105
    have h129 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1108 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1106 2 h128 kg_975_1106
    have h130 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1109 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1108 1 h129 kg_975_1108
    have h131 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1110 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1109 1 h130 kg_975_1109
    have h132 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1112 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1110 2 h131 kg_975_1110
    have h133 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1113 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1112 1 h132 kg_975_1112
    have h134 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1115 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1113 2 h133 kg_975_1113
    have h135 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1117 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1115 2 h134 kg_975_1115
    have h136 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1118 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1117 1 h135 kg_975_1117
    have h137 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1120 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1118 2 h136 kg_975_1118
    have h138 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1123 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1120 3 h137 kg_975_1120
    have h139 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1124 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1123 1 h138 kg_975_1123
    have h140 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1125 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1124 1 h139 kg_975_1124
    have h141 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1126 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1125 1 h140 kg_975_1125
    have h142 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1128 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1126 2 h141 kg_975_1126
    have h143 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1129 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1128 1 h142 kg_975_1128
    have h144 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1130 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1129 1 h143 kg_975_1129
    have h145 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1131 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1130 1 h144 kg_975_1130
    have h146 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1132 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1131 1 h145 kg_975_1131
    have h147 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1133 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1132 1 h146 kg_975_1132
    have h148 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1134 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1133 1 h147 kg_975_1133
    have h149 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1135 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1134 1 h148 kg_975_1134
    have h150 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1137 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1135 2 h149 kg_975_1135
    have h151 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1139 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1137 2 h150 kg_975_1137
    have h152 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1141 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1139 2 h151 kg_975_1139
    have h153 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1142 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1141 1 h152 kg_975_1141
    have h154 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1143 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1142 1 h153 kg_975_1142
    have h155 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1144 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1143 1 h154 kg_975_1143
    have h156 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1145 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1144 1 h155 kg_975_1144
    have h157 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1147 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1145 2 h156 kg_975_1145
    have h158 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1150 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1147 3 h157 kg_975_1147
    have h159 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1151 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1150 1 h158 kg_975_1150
    have h160 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1152 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1151 1 h159 kg_975_1151
    have h161 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1154 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1152 2 h160 kg_975_1152
    have h162 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1156 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1154 2 h161 kg_975_1154
    have h163 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1158 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1156 2 h162 kg_975_1156
    have h164 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1159 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1158 1 h163 kg_975_1158
    have h165 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1161 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1159 2 h164 kg_975_1159
    have h166 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1163 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1161 2 h165 kg_975_1161
    have h167 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1164 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1163 1 h166 kg_975_1163
    have h168 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1165 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1164 1 h167 kg_975_1164
    have h169 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1166 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1165 1 h168 kg_975_1165
    have h170 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1168 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1166 2 h169 kg_975_1166
    have h171 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1170 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1168 2 h170 kg_975_1168
    have h172 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1171 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1170 1 h171 kg_975_1170
    have h173 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1174 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1171 3 h172 kg_975_1171
    have h174 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1177 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1174 3 h173 kg_975_1174
    have h175 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1178 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1177 1 h174 kg_975_1177
    have h176 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1179 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1178 1 h175 kg_975_1178
    have h177 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1182 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1179 3 h176 kg_975_1179
    have h178 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1184 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1182 2 h177 kg_975_1182
    have h179 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1186 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1184 2 h178 kg_975_1184
    have h180 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1187 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1186 1 h179 kg_975_1186
    have h181 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1188 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1187 1 h180 kg_975_1187
    have h182 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1189 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1188 1 h181 kg_975_1188
    have h183 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1190 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1189 1 h182 kg_975_1189
    have h184 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1192 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1190 2 h183 kg_975_1190
    have h185 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1194 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1192 2 h184 kg_975_1192
    have h186 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1197 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1194 3 h185 kg_975_1194
    have h187 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1199 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1197 2 h186 kg_975_1197
    have h188 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1201 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1199 2 h187 kg_975_1199
    have h189 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1202 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1201 1 h188 kg_975_1201
    have h190 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1203 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1202 1 h189 kg_975_1202
    have h191 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1205 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1203 2 h190 kg_975_1203
    have h192 : IPChk.allR (Pts.glueIB K975.lits KW_975) 0 1206 = true := IPChk.allR_join (Pts.glueIB K975.lits KW_975) 0 1205 1 h191 kg_975_1205
    exact h192
  have hlen : K975.lits.length = 1206 := by decide
  intro k h1 h2
  obtain rfl : k = 975 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 975) K975.lits KW_975
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_195 : ∀ k, 976 ≤ k → k < 981 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_976 JW_976 976 5 jr_976
theorem jr6_196 : ∀ k, 981 ≤ k → k < 982 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 942 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 4 = true := kb_981_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 7 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 4 3 h0 kb_981_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 7 6 h1 kb_981_7
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 13 1 h2 kb_981_13
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 14 20 h3 kb_981_14
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 35 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 34 1 h4 kb_981_34
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 41 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 35 6 h5 kb_981_35
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 42 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 41 1 h6 kb_981_41
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 46 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 42 4 h7 kb_981_42
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 47 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 46 1 h8 kb_981_46
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 58 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 47 11 h9 kb_981_47
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 63 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 58 5 h10 kb_981_58
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 65 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 63 2 h11 kb_981_63
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 90 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 65 25 h12 kb_981_65
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 90 95 h13 kb_981_90
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 185 2 h14 kb_981_185
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 187 1 h15 kb_981_187
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 189 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 188 1 h16 kb_981_188
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 191 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 189 2 h17 kb_981_189
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 221 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 191 30 h18 kb_981_191
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 223 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 221 2 h19 kb_981_221
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 223 6 h20 kb_981_223
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 231 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 229 2 h21 kb_981_229
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 291 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 231 60 h22 kb_981_231
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 311 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 291 20 h23 kb_981_291
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 313 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 311 2 h24 kb_981_311
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 342 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 313 29 h25 kb_981_313
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 344 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 342 2 h26 kb_981_342
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 350 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 344 6 h27 kb_981_344
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 352 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 350 2 h28 kb_981_350
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 374 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 352 22 h29 kb_981_352
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 416 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 374 42 h30 kb_981_374
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 416 30 h31 kb_981_416
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 447 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 446 1 h32 kb_981_446
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 449 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 447 2 h33 kb_981_447
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 478 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 449 29 h34 kb_981_449
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 480 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 478 2 h35 kb_981_478
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 486 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 480 6 h36 kb_981_480
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 488 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 486 2 h37 kb_981_486
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 510 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 488 22 h38 kb_981_488
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 559 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 510 49 h39 kb_981_510
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 591 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 559 32 h40 kb_981_559
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 609 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 591 18 h41 kb_981_591
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 609 39 h42 kb_981_609
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 662 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 648 14 h43 kb_981_648
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 662 1 h44 kb_981_662
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 675 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 663 12 h45 kb_981_663
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 677 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 675 2 h46 kb_981_675
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 678 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 677 1 h47 kb_981_677
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 679 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 678 1 h48 kb_981_678
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 679 1 h49 kb_981_679
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 681 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 680 1 h50 kb_981_680
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 683 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 681 2 h51 kb_981_681
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 684 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 683 1 h52 kb_981_683
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 685 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 684 1 h53 kb_981_684
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 686 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 685 1 h54 kb_981_685
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 688 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 686 2 h55 kb_981_686
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 689 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 688 1 h56 kb_981_688
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 689 3 h57 kb_981_689
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 692 1 h58 kb_981_692
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 699 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 693 6 h59 kb_981_693
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 705 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 699 6 h60 kb_981_699
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 705 2 h61 kb_981_705
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 710 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 707 3 h62 kb_981_707
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 711 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 710 1 h63 kb_981_710
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 714 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 711 3 h64 kb_981_711
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 715 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 714 1 h65 kb_981_714
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 719 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 715 4 h66 kb_981_715
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 723 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 719 4 h67 kb_981_719
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 730 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 723 7 h68 kb_981_723
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 732 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 730 2 h69 kb_981_730
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 733 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 732 1 h70 kb_981_732
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 738 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 733 5 h71 kb_981_733
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 738 1 h72 kb_981_738
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 739 1 h73 kb_981_739
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 742 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 740 2 h74 kb_981_740
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 746 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 742 4 h75 kb_981_742
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 747 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 746 1 h76 kb_981_746
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 754 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 747 7 h77 kb_981_747
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 754 3 h78 kb_981_754
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 758 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 757 1 h79 kb_981_757
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 767 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 758 9 h80 kb_981_758
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 768 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 767 1 h81 kb_981_767
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 776 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 768 8 h82 kb_981_768
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 789 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 776 13 h83 kb_981_776
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 796 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 789 7 h84 kb_981_789
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 814 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 796 18 h85 kb_981_796
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 826 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 814 12 h86 kb_981_814
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 858 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 826 32 h87 kb_981_826
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 859 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 858 1 h88 kb_981_858
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 860 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 859 1 h89 kb_981_859
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 862 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 860 2 h90 kb_981_860
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 865 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 862 3 h91 kb_981_862
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 866 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 865 1 h92 kb_981_865
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 867 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 866 1 h93 kb_981_866
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 868 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 867 1 h94 kb_981_867
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 869 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 868 1 h95 kb_981_868
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 870 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 869 1 h96 kb_981_869
    have h98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 871 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 870 1 h97 kb_981_870
    have h99 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 872 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 871 1 h98 kb_981_871
    have h100 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 873 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 872 1 h99 kb_981_872
    have h101 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 874 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 873 1 h100 kb_981_873
    have h102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 876 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 874 2 h101 kb_981_874
    have h103 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 876 2 h102 kb_981_876
    have h104 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 884 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 878 6 h103 kb_981_878
    have h105 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 886 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 884 2 h104 kb_981_884
    have h106 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 890 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 886 4 h105 kb_981_886
    have h107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 907 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 890 17 h106 kb_981_890
    have h108 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 930 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 907 23 h107 kb_981_907
    have h109 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 932 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 930 2 h108 kb_981_930
    have h110 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 935 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 932 3 h109 kb_981_932
    have h111 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 937 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 935 2 h110 kb_981_935
    have h112 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 942 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K981.lits.getD i 0)) 0 937 5 h111 kb_981_937
    exact h112
  have hg : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 942 = true := by
    have h0 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 4 = true := kg_981_0
    have h1 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 7 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 4 3 h0 kg_981_4
    have h2 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 13 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 7 6 h1 kg_981_7
    have h3 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 14 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 13 1 h2 kg_981_13
    have h4 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 34 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 14 20 h3 kg_981_14
    have h5 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 35 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 34 1 h4 kg_981_34
    have h6 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 41 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 35 6 h5 kg_981_35
    have h7 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 42 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 41 1 h6 kg_981_41
    have h8 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 46 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 42 4 h7 kg_981_42
    have h9 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 47 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 46 1 h8 kg_981_46
    have h10 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 58 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 47 11 h9 kg_981_47
    have h11 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 63 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 58 5 h10 kg_981_58
    have h12 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 65 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 63 2 h11 kg_981_63
    have h13 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 90 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 65 25 h12 kg_981_65
    have h14 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 185 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 90 95 h13 kg_981_90
    have h15 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 187 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 185 2 h14 kg_981_185
    have h16 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 188 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 187 1 h15 kg_981_187
    have h17 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 189 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 188 1 h16 kg_981_188
    have h18 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 191 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 189 2 h17 kg_981_189
    have h19 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 221 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 191 30 h18 kg_981_191
    have h20 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 223 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 221 2 h19 kg_981_221
    have h21 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 229 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 223 6 h20 kg_981_223
    have h22 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 231 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 229 2 h21 kg_981_229
    have h23 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 291 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 231 60 h22 kg_981_231
    have h24 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 311 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 291 20 h23 kg_981_291
    have h25 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 313 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 311 2 h24 kg_981_311
    have h26 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 342 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 313 29 h25 kg_981_313
    have h27 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 344 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 342 2 h26 kg_981_342
    have h28 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 350 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 344 6 h27 kg_981_344
    have h29 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 352 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 350 2 h28 kg_981_350
    have h30 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 374 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 352 22 h29 kg_981_352
    have h31 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 416 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 374 42 h30 kg_981_374
    have h32 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 446 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 416 30 h31 kg_981_416
    have h33 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 447 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 446 1 h32 kg_981_446
    have h34 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 449 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 447 2 h33 kg_981_447
    have h35 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 478 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 449 29 h34 kg_981_449
    have h36 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 480 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 478 2 h35 kg_981_478
    have h37 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 486 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 480 6 h36 kg_981_480
    have h38 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 488 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 486 2 h37 kg_981_486
    have h39 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 510 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 488 22 h38 kg_981_488
    have h40 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 559 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 510 49 h39 kg_981_510
    have h41 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 591 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 559 32 h40 kg_981_559
    have h42 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 609 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 591 18 h41 kg_981_591
    have h43 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 648 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 609 39 h42 kg_981_609
    have h44 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 662 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 648 14 h43 kg_981_648
    have h45 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 663 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 662 1 h44 kg_981_662
    have h46 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 675 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 663 12 h45 kg_981_663
    have h47 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 677 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 675 2 h46 kg_981_675
    have h48 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 678 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 677 1 h47 kg_981_677
    have h49 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 679 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 678 1 h48 kg_981_678
    have h50 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 680 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 679 1 h49 kg_981_679
    have h51 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 681 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 680 1 h50 kg_981_680
    have h52 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 683 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 681 2 h51 kg_981_681
    have h53 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 684 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 683 1 h52 kg_981_683
    have h54 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 685 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 684 1 h53 kg_981_684
    have h55 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 686 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 685 1 h54 kg_981_685
    have h56 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 688 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 686 2 h55 kg_981_686
    have h57 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 689 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 688 1 h56 kg_981_688
    have h58 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 692 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 689 3 h57 kg_981_689
    have h59 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 693 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 692 1 h58 kg_981_692
    have h60 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 699 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 693 6 h59 kg_981_693
    have h61 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 705 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 699 6 h60 kg_981_699
    have h62 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 707 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 705 2 h61 kg_981_705
    have h63 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 710 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 707 3 h62 kg_981_707
    have h64 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 711 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 710 1 h63 kg_981_710
    have h65 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 714 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 711 3 h64 kg_981_711
    have h66 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 715 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 714 1 h65 kg_981_714
    have h67 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 719 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 715 4 h66 kg_981_715
    have h68 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 723 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 719 4 h67 kg_981_719
    have h69 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 730 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 723 7 h68 kg_981_723
    have h70 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 732 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 730 2 h69 kg_981_730
    have h71 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 733 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 732 1 h70 kg_981_732
    have h72 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 738 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 733 5 h71 kg_981_733
    have h73 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 739 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 738 1 h72 kg_981_738
    have h74 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 740 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 739 1 h73 kg_981_739
    have h75 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 742 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 740 2 h74 kg_981_740
    have h76 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 746 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 742 4 h75 kg_981_742
    have h77 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 747 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 746 1 h76 kg_981_746
    have h78 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 754 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 747 7 h77 kg_981_747
    have h79 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 757 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 754 3 h78 kg_981_754
    have h80 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 758 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 757 1 h79 kg_981_757
    have h81 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 767 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 758 9 h80 kg_981_758
    have h82 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 768 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 767 1 h81 kg_981_767
    have h83 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 776 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 768 8 h82 kg_981_768
    have h84 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 789 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 776 13 h83 kg_981_776
    have h85 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 796 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 789 7 h84 kg_981_789
    have h86 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 814 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 796 18 h85 kg_981_796
    have h87 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 826 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 814 12 h86 kg_981_814
    have h88 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 858 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 826 32 h87 kg_981_826
    have h89 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 859 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 858 1 h88 kg_981_858
    have h90 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 860 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 859 1 h89 kg_981_859
    have h91 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 862 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 860 2 h90 kg_981_860
    have h92 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 865 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 862 3 h91 kg_981_862
    have h93 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 866 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 865 1 h92 kg_981_865
    have h94 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 867 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 866 1 h93 kg_981_866
    have h95 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 868 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 867 1 h94 kg_981_867
    have h96 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 869 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 868 1 h95 kg_981_868
    have h97 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 870 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 869 1 h96 kg_981_869
    have h98 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 871 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 870 1 h97 kg_981_870
    have h99 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 872 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 871 1 h98 kg_981_871
    have h100 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 873 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 872 1 h99 kg_981_872
    have h101 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 874 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 873 1 h100 kg_981_873
    have h102 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 876 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 874 2 h101 kg_981_874
    have h103 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 878 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 876 2 h102 kg_981_876
    have h104 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 884 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 878 6 h103 kg_981_878
    have h105 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 886 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 884 2 h104 kg_981_884
    have h106 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 890 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 886 4 h105 kg_981_886
    have h107 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 907 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 890 17 h106 kg_981_890
    have h108 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 930 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 907 23 h107 kg_981_907
    have h109 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 932 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 930 2 h108 kg_981_930
    have h110 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 935 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 932 3 h109 kg_981_932
    have h111 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 937 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 935 2 h110 kg_981_935
    have h112 : IPChk.allR (Pts.glueIB K981.lits KW_981) 0 942 = true := IPChk.allR_join (Pts.glueIB K981.lits KW_981) 0 937 5 h111 kg_981_937
    exact h112
  have hlen : K981.lits.length = 942 := by decide
  intro k h1 h2
  obtain rfl : k = 981 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 981) K981.lits KW_981
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_197 : ∀ k, 982 ≤ k → k < 983 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_982 JW_982 982 1 jr_982
theorem jr6_198 : ∀ k, 983 ≤ k → k < 984 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have hb : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 880 = true := by
    have h0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 4 = true := kb_983_0
    have h1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 10 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 4 6 h0 kb_983_4
    have h2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 12 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 10 2 h1 kb_983_10
    have h3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 13 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 12 1 h2 kb_983_12
    have h4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 25 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 13 12 h3 kb_983_13
    have h5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 28 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 25 3 h4 kb_983_25
    have h6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 32 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 28 4 h5 kb_983_28
    have h7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 33 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 32 1 h6 kb_983_32
    have h8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 38 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 33 5 h7 kb_983_33
    have h9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 39 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 38 1 h8 kb_983_38
    have h10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 44 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 39 5 h9 kb_983_39
    have h11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 45 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 44 1 h10 kb_983_44
    have h12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 54 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 45 9 h11 kb_983_45
    have h13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 59 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 54 5 h12 kb_983_54
    have h14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 61 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 59 2 h13 kb_983_59
    have h15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 107 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 61 46 h14 kb_983_61
    have h16 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 185 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 107 78 h15 kb_983_107
    have h17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 187 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 185 2 h16 kb_983_185
    have h18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 188 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 187 1 h17 kb_983_187
    have h19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 190 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 188 2 h18 kb_983_188
    have h20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 193 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 190 3 h19 kb_983_190
    have h21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 194 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 193 1 h20 kb_983_193
    have h22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 195 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 194 1 h21 kb_983_194
    have h23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 197 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 195 2 h22 kb_983_195
    have h24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 227 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 197 30 h23 kb_983_197
    have h25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 229 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 227 2 h24 kb_983_227
    have h26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 235 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 229 6 h25 kb_983_229
    have h27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 237 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 235 2 h26 kb_983_235
    have h28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 292 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 237 55 h27 kb_983_237
    have h29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 319 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 292 27 h28 kb_983_292
    have h30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 320 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 319 1 h29 kb_983_319
    have h31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 322 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 320 2 h30 kb_983_320
    have h32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 351 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 322 29 h31 kb_983_322
    have h33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 353 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 351 2 h32 kb_983_351
    have h34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 359 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 353 6 h33 kb_983_353
    have h35 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 361 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 359 2 h34 kb_983_359
    have h36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 383 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 361 22 h35 kb_983_361
    have h37 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 409 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 383 26 h36 kb_983_383
    have h38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 445 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 409 36 h37 kb_983_409
    have h39 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 446 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 445 1 h38 kb_983_445
    have h40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 448 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 446 2 h39 kb_983_446
    have h41 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 477 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 448 29 h40 kb_983_448
    have h42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 479 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 477 2 h41 kb_983_477
    have h43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 485 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 479 6 h42 kb_983_479
    have h44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 487 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 485 2 h43 kb_983_485
    have h45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 509 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 487 22 h44 kb_983_487
    have h46 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 529 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 509 20 h45 kb_983_509
    have h47 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 576 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 529 47 h46 kb_983_529
    have h48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 600 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 576 24 h47 kb_983_576
    have h49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 635 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 600 35 h48 kb_983_600
    have h50 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 637 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 635 2 h49 kb_983_635
    have h51 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 648 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 637 11 h50 kb_983_637
    have h52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 649 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 648 1 h51 kb_983_648
    have h53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 661 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 649 12 h52 kb_983_649
    have h54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 663 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 661 2 h53 kb_983_661
    have h55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 665 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 663 2 h54 kb_983_663
    have h56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 666 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 665 1 h55 kb_983_665
    have h57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 667 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 666 1 h56 kb_983_666
    have h58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 668 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 667 1 h57 kb_983_667
    have h59 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 669 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 668 1 h58 kb_983_668
    have h60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 670 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 669 1 h59 kb_983_669
    have h61 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 671 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 670 1 h60 kb_983_670
    have h62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 672 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 671 1 h61 kb_983_671
    have h63 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 673 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 672 1 h62 kb_983_672
    have h64 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 676 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 673 3 h63 kb_983_673
    have h65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 680 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 676 4 h64 kb_983_676
    have h66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 687 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 680 7 h65 kb_983_680
    have h67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 690 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 687 3 h66 kb_983_687
    have h68 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 691 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 690 1 h67 kb_983_690
    have h69 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 692 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 691 1 h68 kb_983_691
    have h70 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 693 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 692 1 h69 kb_983_692
    have h71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 696 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 693 3 h70 kb_983_693
    have h72 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 700 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 696 4 h71 kb_983_696
    have h73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 707 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 700 7 h72 kb_983_700
    have h74 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 713 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 707 6 h73 kb_983_707
    have h75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 722 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 713 9 h74 kb_983_713
    have h76 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 734 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 722 12 h75 kb_983_722
    have h77 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 736 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 734 2 h76 kb_983_734
    have h78 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 739 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 736 3 h77 kb_983_736
    have h79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 740 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 739 1 h78 kb_983_739
    have h80 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 747 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 740 7 h79 kb_983_740
    have h81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 757 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 747 10 h80 kb_983_747
    have h82 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 783 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 757 26 h81 kb_983_757
    have h83 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 797 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 783 14 h82 kb_983_783
    have h84 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 815 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 797 18 h83 kb_983_797
    have h85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 817 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 815 2 h84 kb_983_815
    have h86 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 818 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 817 1 h85 kb_983_817
    have h87 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 819 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 818 1 h86 kb_983_818
    have h88 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 820 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 819 1 h87 kb_983_819
    have h89 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 821 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 820 1 h88 kb_983_820
    have h90 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 822 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 821 1 h89 kb_983_821
    have h91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 824 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 822 2 h90 kb_983_822
    have h92 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 825 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 824 1 h91 kb_983_824
    have h93 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 827 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 825 2 h92 kb_983_825
    have h94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 828 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 827 1 h93 kb_983_827
    have h95 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 849 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 828 21 h94 kb_983_828
    have h96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 878 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 849 29 h95 kb_983_849
    have h97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 880 = true := IPChk.allR_join (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K983.lits.getD i 0)) 0 878 2 h96 kb_983_878
    exact h97
  have hg : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 880 = true := by
    have h0 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 4 = true := kg_983_0
    have h1 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 10 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 4 6 h0 kg_983_4
    have h2 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 12 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 10 2 h1 kg_983_10
    have h3 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 13 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 12 1 h2 kg_983_12
    have h4 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 25 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 13 12 h3 kg_983_13
    have h5 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 28 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 25 3 h4 kg_983_25
    have h6 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 32 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 28 4 h5 kg_983_28
    have h7 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 33 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 32 1 h6 kg_983_32
    have h8 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 38 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 33 5 h7 kg_983_33
    have h9 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 39 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 38 1 h8 kg_983_38
    have h10 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 44 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 39 5 h9 kg_983_39
    have h11 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 45 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 44 1 h10 kg_983_44
    have h12 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 54 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 45 9 h11 kg_983_45
    have h13 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 59 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 54 5 h12 kg_983_54
    have h14 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 61 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 59 2 h13 kg_983_59
    have h15 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 107 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 61 46 h14 kg_983_61
    have h16 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 185 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 107 78 h15 kg_983_107
    have h17 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 187 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 185 2 h16 kg_983_185
    have h18 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 188 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 187 1 h17 kg_983_187
    have h19 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 190 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 188 2 h18 kg_983_188
    have h20 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 193 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 190 3 h19 kg_983_190
    have h21 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 194 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 193 1 h20 kg_983_193
    have h22 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 195 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 194 1 h21 kg_983_194
    have h23 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 197 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 195 2 h22 kg_983_195
    have h24 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 227 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 197 30 h23 kg_983_197
    have h25 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 229 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 227 2 h24 kg_983_227
    have h26 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 235 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 229 6 h25 kg_983_229
    have h27 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 237 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 235 2 h26 kg_983_235
    have h28 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 292 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 237 55 h27 kg_983_237
    have h29 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 319 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 292 27 h28 kg_983_292
    have h30 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 320 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 319 1 h29 kg_983_319
    have h31 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 322 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 320 2 h30 kg_983_320
    have h32 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 351 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 322 29 h31 kg_983_322
    have h33 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 353 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 351 2 h32 kg_983_351
    have h34 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 359 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 353 6 h33 kg_983_353
    have h35 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 361 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 359 2 h34 kg_983_359
    have h36 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 383 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 361 22 h35 kg_983_361
    have h37 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 409 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 383 26 h36 kg_983_383
    have h38 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 445 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 409 36 h37 kg_983_409
    have h39 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 446 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 445 1 h38 kg_983_445
    have h40 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 448 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 446 2 h39 kg_983_446
    have h41 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 477 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 448 29 h40 kg_983_448
    have h42 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 479 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 477 2 h41 kg_983_477
    have h43 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 485 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 479 6 h42 kg_983_479
    have h44 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 487 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 485 2 h43 kg_983_485
    have h45 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 509 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 487 22 h44 kg_983_487
    have h46 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 529 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 509 20 h45 kg_983_509
    have h47 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 576 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 529 47 h46 kg_983_529
    have h48 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 600 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 576 24 h47 kg_983_576
    have h49 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 635 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 600 35 h48 kg_983_600
    have h50 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 637 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 635 2 h49 kg_983_635
    have h51 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 648 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 637 11 h50 kg_983_637
    have h52 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 649 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 648 1 h51 kg_983_648
    have h53 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 661 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 649 12 h52 kg_983_649
    have h54 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 663 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 661 2 h53 kg_983_661
    have h55 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 665 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 663 2 h54 kg_983_663
    have h56 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 666 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 665 1 h55 kg_983_665
    have h57 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 667 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 666 1 h56 kg_983_666
    have h58 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 668 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 667 1 h57 kg_983_667
    have h59 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 669 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 668 1 h58 kg_983_668
    have h60 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 670 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 669 1 h59 kg_983_669
    have h61 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 671 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 670 1 h60 kg_983_670
    have h62 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 672 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 671 1 h61 kg_983_671
    have h63 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 673 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 672 1 h62 kg_983_672
    have h64 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 676 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 673 3 h63 kg_983_673
    have h65 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 680 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 676 4 h64 kg_983_676
    have h66 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 687 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 680 7 h65 kg_983_680
    have h67 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 690 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 687 3 h66 kg_983_687
    have h68 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 691 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 690 1 h67 kg_983_690
    have h69 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 692 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 691 1 h68 kg_983_691
    have h70 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 693 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 692 1 h69 kg_983_692
    have h71 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 696 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 693 3 h70 kg_983_693
    have h72 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 700 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 696 4 h71 kg_983_696
    have h73 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 707 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 700 7 h72 kg_983_700
    have h74 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 713 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 707 6 h73 kg_983_707
    have h75 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 722 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 713 9 h74 kg_983_713
    have h76 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 734 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 722 12 h75 kg_983_722
    have h77 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 736 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 734 2 h76 kg_983_734
    have h78 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 739 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 736 3 h77 kg_983_736
    have h79 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 740 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 739 1 h78 kg_983_739
    have h80 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 747 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 740 7 h79 kg_983_740
    have h81 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 757 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 747 10 h80 kg_983_747
    have h82 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 783 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 757 26 h81 kg_983_757
    have h83 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 797 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 783 14 h82 kg_983_783
    have h84 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 815 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 797 18 h83 kg_983_797
    have h85 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 817 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 815 2 h84 kg_983_815
    have h86 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 818 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 817 1 h85 kg_983_817
    have h87 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 819 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 818 1 h86 kg_983_818
    have h88 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 820 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 819 1 h87 kg_983_819
    have h89 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 821 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 820 1 h88 kg_983_820
    have h90 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 822 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 821 1 h89 kg_983_821
    have h91 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 824 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 822 2 h90 kg_983_822
    have h92 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 825 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 824 1 h91 kg_983_824
    have h93 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 827 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 825 2 h92 kg_983_825
    have h94 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 828 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 827 1 h93 kg_983_827
    have h95 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 849 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 828 21 h94 kg_983_828
    have h96 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 878 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 849 29 h95 kg_983_849
    have h97 : IPChk.allR (Pts.glueIB K983.lits KW_983) 0 880 = true := IPChk.allR_join (Pts.glueIB K983.lits KW_983) 0 878 2 h96 kg_983_878
    exact h97
  have hlen : K983.lits.length = 880 := by decide
  intro k h1 h2
  obtain rfl : k = 983 := by omega
  exact Pts.jobOK_of_parts CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le (HT.entry 983) K983.lits KW_983
    (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) (by decide +kernel)
    (by decide +kernel)
theorem jr6_199 : ∀ k, 984 ≤ k → k < 985 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) :=
  Pts.jobs_of_allR CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR Pts.H707.UB_eq Pts.H707.UBR_eq Pts.H707.UB_le HT.entry JL_984 JW_984 984 1 jr_984

theorem grp6_6 : ∀ k, 846 ≤ k → k < 985 → JobOK CL Pts.H707.sl Pts.H707.UB (HT.entry k) := by
  have a0 := jr6_172
  have a1 := Pts.fa_join a0 jr6_173
  have a2 := Pts.fa_join a1 jr6_174
  have a3 := Pts.fa_join a2 jr6_175
  have a4 := Pts.fa_join a3 jr6_176
  have a5 := Pts.fa_join a4 jr6_177
  have a6 := Pts.fa_join a5 jr6_178
  have a7 := Pts.fa_join a6 jr6_179
  have a8 := Pts.fa_join a7 jr6_180
  have a9 := Pts.fa_join a8 jr6_181
  have a10 := Pts.fa_join a9 jr6_182
  have a11 := Pts.fa_join a10 jr6_183
  have a12 := Pts.fa_join a11 jr6_184
  have a13 := Pts.fa_join a12 jr6_185
  have a14 := Pts.fa_join a13 jr6_186
  have a15 := Pts.fa_join a14 jr6_187
  have a16 := Pts.fa_join a15 jr6_188
  have a17 := Pts.fa_join a16 jr6_189
  have a18 := Pts.fa_join a17 jr6_190
  have a19 := Pts.fa_join a18 jr6_191
  have a20 := Pts.fa_join a19 jr6_192
  have a21 := Pts.fa_join a20 jr6_193
  have a22 := Pts.fa_join a21 jr6_194
  have a23 := Pts.fa_join a22 jr6_195
  have a24 := Pts.fa_join a23 jr6_196
  have a25 := Pts.fa_join a24 jr6_197
  have a26 := Pts.fa_join a25 jr6_198
  have a27 := Pts.fa_join a26 jr6_199
  exact a27

end B334.E1x.Pts.S707
