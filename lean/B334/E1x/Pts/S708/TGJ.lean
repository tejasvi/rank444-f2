import B334.E1x.Pts.S708.TopL
import B334.E1x.Pts.S708.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.S708.TG0
import B334.E1x.Pts.S708.TG1
import B334.E1x.Pts.S708.TG2
import B334.E1x.Pts.S708.TG3
import B334.E1x.Pts.S708.TG4
import B334.E1x.Pts.S708.TG5
import B334.E1x.Pts.S708.TG6
import B334.E1x.Pts.S708.TG7
import B334.E1x.Pts.S708.TG8
import B334.E1x.Pts.S708.TG9
import B334.E1x.Pts.S708.TG10
import B334.E1x.Pts.S708.TG11
import B334.E1x.Pts.S708.TG12
import B334.E1x.Pts.S708.TG13
import B334.E1x.Pts.S708.TG14
import B334.E1x.Pts.S708.TG15
import B334.E1x.Pts.S708.TG16
import B334.E1x.Pts.S708.TG17
import B334.E1x.Pts.S708.TG18
import B334.E1x.Pts.S708.TG19
import B334.E1x.Pts.S708.TG20
import B334.E1x.Pts.S708.TG21
import B334.E1x.Pts.S708.TG22
import B334.E1x.Pts.S708.TG23

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The joined top-chain glue facts of `S708`: the generated Fin's `topGlue` proof -/

namespace B334.E1x.Pts.S708

theorem topGlueJ : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 NT = true := by
  have h0 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 617 = true := tgm_0
  have h1 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 1196 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 617 579 h0 tgm_617
  have h2 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 1949 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 1196 753 h1 tgm_1196
  have h3 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 2381 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 1949 432 h2 tgm_1949
  have h4 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 2813 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 2381 432 h3 tgm_2381
  have h5 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 3316 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 2813 503 h4 tgm_2813
  have h6 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 3742 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 3316 426 h5 tgm_3316
  have h7 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 4285 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 3742 543 h6 tgm_3742
  have h8 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 4743 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 4285 458 h7 tgm_4285
  have h9 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5221 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 4743 478 h8 tgm_4743
  have h10 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5648 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5221 427 h9 tgm_5221
  have h11 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5966 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5648 318 h10 tgm_5648
  have h12 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6356 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 5966 390 h11 tgm_5966
  have h13 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6643 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6356 287 h12 tgm_6356
  have h14 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6924 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6643 281 h13 tgm_6643
  have h15 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 7327 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 6924 403 h14 tgm_6924
  have h16 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 7720 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 7327 393 h15 tgm_7327
  have h17 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8124 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 7720 404 h16 tgm_7720
  have h18 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8545 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8124 421 h17 tgm_8124
  have h19 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8793 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8545 248 h18 tgm_8545
  have h20 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9035 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 8793 242 h19 tgm_8793
  have h21 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9292 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9035 257 h20 tgm_9035
  have h22 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9511 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9292 219 h21 tgm_9292
  have h23 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9679 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 9511 168 h22 tgm_9511
  exact h23

end B334.E1x.Pts.S708
