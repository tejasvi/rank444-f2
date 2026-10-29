import B334.MethodK.Rows.R11D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 11: K-W chunk 1 of 8 (masks 512 … 1023). GENERATED; do not edit. -/

namespace B334.MethodK.R11
open B334.MethodK B334.Core

theorem kW1 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (2 * 0) Yz 12 12 true (1 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R11
