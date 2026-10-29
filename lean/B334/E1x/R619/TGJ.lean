import B334.E1x.R619.TG0
import B334.E1x.R619.TopL
import B334.E1x.R619.HT
import B334.E1x.IPChk

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The joined top-chain glue facts of `R619`: the generated Fin's `topGlue` proof -/

namespace B334.E1x.R619

theorem topGlueJ : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 NT = true := by
  have h0 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 15 = true := tg_0
  have h1 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 54 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 15 39 h0 tg_15
  have h2 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 84 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 54 30 h1 tg_54
  have h3 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 103 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 84 19 h2 tg_84
  have h4 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 116 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 103 13 h3 tg_103
  have h5 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 122 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 116 6 h4 tg_116
  have h6 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 134 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 122 12 h5 tg_122
  have h7 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 140 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 134 6 h6 tg_134
  have h8 : IPChk.allR (GJ.glueWB Top.lits nJ HT.entry Wf) 0 142 = true := IPChk.allR_join (GJ.glueWB Top.lits nJ HT.entry Wf) 0 140 2 h7 tg_140
  rw [show NT = 142 by decide +kernel]
  exact h8

end B334.E1x.R619
