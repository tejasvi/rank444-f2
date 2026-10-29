import B334.E1x.Pts.S707.TopL
import B334.E1x.Pts.S707.HT
import B334.E1x.Pts.ChkB
import B334.E1x.Pts.S707.TG0
import B334.E1x.Pts.S707.TG1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The joined top-chain glue facts of `S707` (stage707_v6): the v5 Fin's `topGlue` proof -/

namespace B334.E1x.Pts.S707

theorem topGlueJ : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 NT = true := by
  have h0 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 28 = true := tg_0
  have h1 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 71 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 28 43 h0 tg_28
  have h2 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 203 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 71 132 h1 tg_71
  have h3 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 265 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 203 62 h2 tg_203
  have h4 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 315 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 265 50 h3 tg_265
  have h5 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 364 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 315 49 h4 tg_315
  have h6 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 391 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 364 27 h5 tg_364
  have h7 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 430 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 391 39 h6 tg_391
  have h8 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 466 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 430 36 h7 tg_430
  have h9 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 491 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 466 25 h8 tg_466
  have h10 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 527 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 491 36 h9 tg_491
  have h11 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 557 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 527 30 h10 tg_527
  have h12 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 588 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 557 31 h11 tg_557
  have h13 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 616 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 588 28 h12 tg_588
  have h14 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 651 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 616 35 h13 tg_616
  have h15 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 677 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 651 26 h14 tg_651
  have h16 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 708 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 677 31 h15 tg_677
  have h17 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 733 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 708 25 h16 tg_708
  have h18 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 769 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 733 36 h17 tg_733
  have h19 : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) 0 789 = true := IPChk.allR_join (Pts.glueWB Top.lits nJ HT.entry Wf) 0 769 20 h18 tg_769
  exact h19

end B334.E1x.Pts.S707
