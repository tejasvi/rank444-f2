import B334.E1x.G.Hdr
import B334.E1x.AxCheck

/-! Axiom gate for the E1G soundness stack of ⟨3,3,4⟩ (not part of the library). -/

#assert_std_axioms B334.E1x.RT.perp9_bit
#assert_std_axioms B334.E1x.RT.kerM9_testBit
#assert_std_axioms B334.E1x.RT.par_xor9
#assert_std_axioms B334.E1x.E1GS.stEq_reach
#assert_std_axioms B334.E1x.E1GS.fixes_sem
#assert_std_axioms B334.E1x.E1GS.node_sound
#assert_std_axioms B334.E1x.E1GS.block_sound
#assert_std_axioms B334.E1x.E1GS.chain_sound
#assert_std_axioms B334.E1x.E1GS.slot_valid
#assert_std_axioms B334.E1x.E1GS.noDecomp_of_leafS
#assert_std_axioms B334.E1x.E1GS.leaf_bridge_nd
#assert_std_axioms B334.E1x.E1GS.leafOK_bridge
#assert_std_axioms B334.E1x.E1GS.xOf_act
#assert_std_axioms B334.E1x.E1GS.e1_sound
#assert_std_axioms B334.E1x.E1GS.chain_sound_ext
#assert_std_axioms B334.E1x.E1GS.e1_sound_ext
#assert_std_axioms B334.E1x.E1GS.jobOK_hdr
