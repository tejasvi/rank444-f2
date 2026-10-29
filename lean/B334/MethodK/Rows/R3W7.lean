import B334.MethodK.Rows.R3D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 3: K-W chunk 7 of 8 (masks 3584 … 4095). GENERATED; do not edit. -/

namespace B334.MethodK.R3
open B334.MethodK B334.Core

theorem kW7 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (1 * 0) Yz 12 12 true (7 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R3
