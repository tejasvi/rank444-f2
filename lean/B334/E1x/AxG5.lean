import B334.E1x.P.Hdr
import B334.E1x.RTE
import B334.E1x.AxCheck

/-! Axiom gate for the E1P soundness stack and the row-table entry layer of ⟨3,3,4⟩ (not
part of the library). -/

#assert_std_axioms B334.E1x.E1PS.node_sound
#assert_std_axioms B334.E1x.E1PS.block_sound
#assert_std_axioms B334.E1x.E1PS.chain_sound
#assert_std_axioms B334.E1x.E1PS.slot_valid
#assert_std_axioms B334.E1x.E1PS.noDecomp_of_leafS
#assert_std_axioms B334.E1x.E1PS.leafOK_bridge
#assert_std_axioms B334.E1x.E1PS.e1_sound
#assert_std_axioms B334.E1x.E1PS.e1_sound_ext
#assert_std_axioms B334.E1x.E1PS.jobOK_hdr
#assert_std_axioms B334.E1x.TransBits.trans_testBit
#assert_std_axioms B334.E1x.RT.spanM_ind
#assert_std_axioms B334.E1x.RT.kM_testBit
#assert_std_axioms B334.E1x.RT.entry_sound
#assert_std_axioms B334.E1x.RT.classFact_of_quotLB
