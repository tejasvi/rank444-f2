import B334.E1x.RB.RunsAll2
import B334.E1x.RB.BatchMulti

/-! # The run theorems of all E1G runs: `RBRuns2.runsAll` (352 classes) and the 15 multi-trace leaf runs
(`RBatchMulti.runs`) as one `Tab2.RunsFor` fact -/

namespace B334.E1x.RBRuns3
open B334.Tab2

theorem runsAll : RunsFor ((RBRuns.L ++ [27, 30, 40, 59, 81, 90, 291, 31, 84, 301, 610, 663, 656, 671, 666, 655, 684, 665,
  685, 661, 670, 668, 674, 657, 664, 659, 669, 662, 654, 675, 615, 613, 658, 696]) ++ [672, 618, 619, 660, 667, 673, 677, 678, 679, 680, 681, 682, 683, 686, 687]) :=
  runs_append RBRuns2.runsAll RBatchMulti.runs

end B334.E1x.RBRuns3
