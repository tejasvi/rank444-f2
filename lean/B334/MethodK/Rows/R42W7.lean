import B334.MethodK.Rows.R42D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 42: K-W chunk 7 of 32 (masks 896 … 1023). GENERATED; do not edit. -/

namespace B334.MethodK.R42
open B334.MethodK B334.Core

theorem kW7 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (7 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R42
