import B334.MethodK.Rows.R35D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 35: K-W chunk 3 of 32 (masks 384 … 511). GENERATED; do not edit. -/

namespace B334.MethodK.R35
open B334.MethodK B334.Core

theorem kW3 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (3 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R35
