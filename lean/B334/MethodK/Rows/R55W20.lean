import B334.MethodK.Rows.R55D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 55: K-W chunk 20 of 64 (masks 1280 … 1343). GENERATED; do not edit. -/

namespace B334.MethodK.R55
open B334.MethodK B334.Core

theorem kW20 : B334.Core.allLT 64 (fun i => kwAt M0r Nr (8 * 4) Yz 12 20 false (20 * 64 + i)) = true := by
  decide +kernel

end B334.MethodK.R55
