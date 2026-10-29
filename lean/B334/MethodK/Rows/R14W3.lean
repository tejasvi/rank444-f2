import B334.MethodK.Rows.R14D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 14: K-W chunk 3 of 8 (masks 1536 … 2047). GENERATED; do not edit. -/

namespace B334.MethodK.R14
open B334.MethodK B334.Core

theorem kW3 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (2 * 0) Yz 12 12 true (3 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R14
