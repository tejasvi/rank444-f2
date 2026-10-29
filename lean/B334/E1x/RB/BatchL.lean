import B334.E1x.I691.Fin
import B334.E1x.I692.Fin
import B334.E1x.I693t.Fin
import B334.E1x.I697.Fin
import B334.E1x.I702.Fin
import B334.E1x.I705.Fin
import B334.Tab2.Dispatch

/-! # The run theorems of the six lines done one by one (691, 692, 693, 697, 702, 705) as one `Tab2.RunsFor` fact
(the six run theorems). Line 692 has hex-literal entries, the others table mode (line 693 from `I693t`). -/

namespace B334.E1x.RBatchL
open B334.Tab2

theorem runs : RunsFor [691, 692, 693, 697, 702, 705] :=
  runs_cons I691.run_691 (runs_cons I692.run_692 (runs_cons I693t.run_693 (runs_cons I697.run_697
    (runs_cons I702.run_702 (runs_cons I705.run_705 runs_nil)))))

end B334.E1x.RBatchL
