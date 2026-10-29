import B334.E1x.R619.TB0
import B334.E1x.R619.TB1
import B334.E1x.R619.TB2
import B334.E1x.R619.TB3
import B334.E1x.R619.TB4
import B334.E1x.R619.TopL
import B334.E1x.R619.HT
import B334.E1x.IPChk

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The joined top-chain block facts of `R619`: the generated Fin's `topBlk` proof -/

namespace B334.E1x.R619

theorem topBlkJ : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 NT = true := by
  have h0 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 2 = true := tb_0
  have h1 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 3 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 2 1 h0 tb_2
  have h2 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 5 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 3 2 h1 tb_3
  have h3 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 8 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 5 3 h2 tb_5
  have h4 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 14 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 8 6 h3 tb_8
  have h5 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 24 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 14 10 h4 tb_14
  have h6 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 34 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 24 10 h5 tb_24
  have h7 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 43 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 34 9 h6 tb_34
  have h8 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 53 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 43 10 h7 tb_43
  have h9 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 60 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 53 7 h8 tb_53
  have h10 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 67 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 60 7 h9 tb_60
  have h11 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 77 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 67 10 h10 tb_67
  have h12 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 84 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 77 7 h11 tb_77
  have h13 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 86 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 84 2 h12 tb_84
  have h14 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 92 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 86 6 h13 tb_86
  have h15 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 93 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 92 1 h14 tb_92
  have h16 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 102 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 93 9 h15 tb_93
  have h17 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 103 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 102 1 h16 tb_102
  have h18 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 110 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 103 7 h17 tb_103
  have h19 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 113 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 110 3 h18 tb_110
  have h20 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 114 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 113 1 h19 tb_113
  have h21 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 115 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 114 1 h20 tb_114
  have h22 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 116 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 115 1 h21 tb_115
  have h23 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 117 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 116 1 h22 tb_116
  have h24 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 118 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 117 1 h23 tb_117
  have h25 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 119 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 118 1 h24 tb_118
  have h26 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 120 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 119 1 h25 tb_119
  have h27 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 121 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 120 1 h26 tb_120
  have h28 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 122 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 121 1 h27 tb_121
  have h29 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 124 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 122 2 h28 tb_122
  have h30 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 130 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 124 6 h29 tb_124
  have h31 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 131 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 130 1 h30 tb_130
  have h32 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 132 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 131 1 h31 tb_131
  have h33 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 133 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 132 1 h32 tb_132
  have h34 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 134 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 133 1 h33 tb_133
  have h35 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 135 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 134 1 h34 tb_134
  have h36 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 136 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 135 1 h35 tb_135
  have h37 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 137 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 136 1 h36 tb_136
  have h38 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 138 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 137 1 h37 tb_137
  have h39 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 139 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 138 1 h38 tb_138
  have h40 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 140 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 139 1 h39 tb_139
  have h41 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 141 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 140 1 h40 tb_140
  have h42 : IPChk.allR (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 142 = true := IPChk.allR_join (fun i => E1G.block C sl UB UBR (Top.lits.getD i 0)) 0 141 1 h41 tb_141
  rw [show NT = 142 by decide +kernel]
  exact h42

end B334.E1x.R619
