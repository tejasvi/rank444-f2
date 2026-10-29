import B334.MethodK.Rows.R12D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 12: K-W chunk 1 of 2 (masks 128 … 255). GENERATED; do not edit. -/

namespace B334.MethodK.R12
open B334.MethodK B334.Core

theorem kW1 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 8 true (1 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R12
