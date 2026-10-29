import B334.MethodK.Rows.R33D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 33: K-W chunk 29 of 32 (masks 3712 … 3839). GENERATED; do not edit. -/

namespace B334.MethodK.R33
open B334.MethodK B334.Core

theorem kW29 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 4) Yz 12 12 true (29 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R33
