import B334.MethodK.Rows.R52D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 52: K-W chunk 11 of 32 (masks 1408 … 1535). GENERATED; do not edit. -/

namespace B334.MethodK.R52
open B334.MethodK B334.Core

theorem kW11 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (11 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R52
