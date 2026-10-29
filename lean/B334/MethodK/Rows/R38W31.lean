import B334.MethodK.Rows.R38D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 38: K-W chunk 31 of 32 (masks 3968 … 4095). GENERATED; do not edit. -/

namespace B334.MethodK.R38
open B334.MethodK B334.Core

theorem kW31 : B334.Core.allLT 128 (fun i => kwAt M0r Nr (4 * 8) Yz 12 12 true (31 * 128 + i)) = true := by
  decide +kernel

end B334.MethodK.R38
