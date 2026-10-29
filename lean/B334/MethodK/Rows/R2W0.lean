import B334.MethodK.Rows.R2D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 2: K-W chunk 0 of 1 (masks 0 … 255). GENERATED; do not edit. -/

namespace B334.MethodK.R2
open B334.MethodK B334.Core

theorem kW0 : B334.Core.allLT 256 (fun i => kwAt M0r Nr (1 * 0) Yz 8 8 true (0 * 256 + i)) = true := by
  decide +kernel

end B334.MethodK.R2
