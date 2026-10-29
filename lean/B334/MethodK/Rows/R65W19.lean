import B334.MethodK.Rows.R65D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 65: K-W chunk 19 of 64 (masks 1216 … 1279). GENERATED; do not edit. -/

namespace B334.MethodK.R65
open B334.MethodK B334.Core

theorem kW19 : B334.Core.allLT 64 (fun i => kwAt M0r Nr (8 * 4) Yz 12 20 false (19 * 64 + i)) = true := by
  decide +kernel

end B334.MethodK.R65
