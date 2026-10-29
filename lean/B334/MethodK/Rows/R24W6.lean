import B334.MethodK.Rows.R24D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 24: K-W chunk 6 of 8 (masks 3072 … 3583). GENERATED; do not edit. -/

namespace B334.MethodK.R24
open B334.MethodK B334.Core

theorem kW6 : B334.Core.allLT 512 (fun i => kwAt M0r Nr (3 * 0) Yz 12 12 true (6 * 512 + i)) = true := by
  decide +kernel

end B334.MethodK.R24
