import B334.MethodK.Rows.R45D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 45: K-W chunk 21 of 32 (masks 2688 … 2815). GENERATED; do not edit. -/

namespace B334.MethodK.R45
open B334.MethodK B334.Core

theorem kW21 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (21 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R45
