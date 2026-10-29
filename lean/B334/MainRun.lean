import B334.Final
import B334.E1x.RB.RunsAll3
import B334.E1x.Pts.S707.Fin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The class facts from the E1 production, and the unconditional P707 bound

* `run_cov`: the class list of `RBRuns3.runsAll` covers every class with `routeOf c = 2` and `lbOf c ≠ 0` (the check
  tested early in `Test/RunCovTest.lean`);
* `runHyp : Tab2.RunHyp`, through `Tab2.runHyp_of_list`;
* `classFacts : ClassFacts`, through `Tab2.hcls_all`;
* `quot707 : QuotLB T334 P707 26`, the point-707 run with its hypothesis discharged. -/

namespace B334

open B334.Tab2

theorem run_cov : (List.range nCls).all (fun c => routeOf c != 2 || lbOf c == 0 ||
    ((B334.E1x.RBRuns.L ++ [27, 30, 40, 59, 81, 90, 291, 31, 84, 301, 610, 663, 656, 671, 666, 655, 684, 665, 685,
      661, 670, 668, 674, 657, 664, 659, 669, 662, 654, 675, 615, 613, 658, 696]) ++
      [672, 618, 619, 660, 667, 673, 677, 678, 679, 680, 681, 682, 683, 686, 687]).contains c) = true := by
  decide +kernel

/-- every class on an E1 route is valid given the higher-dimensional classes -/
theorem runHyp : Tab2.RunHyp := Tab2.runHyp_of_list _ B334.E1x.RBRuns3.runsAll run_cov

/-- every class the point IPs use is valid at the bound they use -/
theorem classFacts : ClassFacts := Tab2.hcls_all runHyp

/-- **The P707 bound**, unconditional. -/
theorem quot707 : QuotLB T334 P707 26 := B334.E1x.Pts.S707.h707 classFacts

end B334

#print axioms B334.runHyp
#print axioms B334.classFacts
#print axioms B334.quot707
