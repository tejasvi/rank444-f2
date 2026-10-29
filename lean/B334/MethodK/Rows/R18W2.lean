import B334.MethodK.Rows.R18D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 18: K-W chunk 2 of 8 (masks 1024 … 1535). GENERATED; do not edit. -/

namespace B334.MethodK.R18
open B334.MethodK B334.Core

theorem kW2 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (2 * 0) Yz 12 12 true (2 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R18
