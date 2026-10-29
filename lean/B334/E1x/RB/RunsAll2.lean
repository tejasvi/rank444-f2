import B334.E1x.RB.RunsAll
import B334.E1x.RB.BatchLeaf1

/-! # The run theorems of the simple E1G runs (318 classes, `RBRuns.runsAll`) and of the single-trace leaf runs
plus class 696 (34 classes, `RBatchLeaf1.runs`) as one `Tab2.RunsFor` fact -/

namespace B334.E1x.RBRuns2
open B334.Tab2

theorem runsAll : RunsFor (RBRuns.L ++ [
  27, 30, 40, 59, 81, 90, 291, 31, 84, 301, 610, 663, 656, 671, 666, 655, 684, 665, 685, 661, 670, 668, 674, 657, 664, 659, 669, 662, 654, 675, 615, 613, 658, 696]) :=
  runs_append RBRuns.runsAll RBatchLeaf1.runs

end B334.E1x.RBRuns2
