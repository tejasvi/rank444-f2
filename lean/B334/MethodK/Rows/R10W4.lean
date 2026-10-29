import B334.MethodK.Rows.R10D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 10: K-W chunk 4 of 8 (masks 2048 … 2559). GENERATED; do not edit. -/

namespace B334.MethodK.R10
open B334.MethodK B334.Core

theorem kW4 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (2 * 0) Yz 12 12 true (4 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R10
