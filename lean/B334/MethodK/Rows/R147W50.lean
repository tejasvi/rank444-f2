import B334.MethodK.Rows.R147D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 147: K-W chunk 50 of 64 (masks 3200 … 3263). GENERATED; do not edit. -/

namespace B334.MethodK.R147
open B334.MethodK B334.Core

theorem kW50 : B334.Core.allLT 64 (fun i => kwAt M0r Nr (4 * 8) Yz 12 16 false (50 * 64 + i)) = true := by
  decide +kernel

end B334.MethodK.R147
