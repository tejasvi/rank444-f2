import B334.MethodK.Rows.R38D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 38: K-W chunk 8 of 32 (masks 1024 … 1151). GENERATED; do not edit. -/

namespace B334.MethodK.R38
open B334.MethodK B334.Core

theorem kW8 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (8 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R38
