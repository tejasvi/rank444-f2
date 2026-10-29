import B334.MethodK.Rows.R16D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 16: K-W chunk 29 of 64 (masks 1856 … 1919). GENERATED; do not edit. -/

namespace B334.MethodK.R16
open B334.MethodK B334.Core

theorem kW29 : B334.Core.allLT 64 (fun i => kwAt M0r Nr (8 * 4) Yz 12 16 false (29 * 64 + i)) = true := by
  decide +kernel

end B334.MethodK.R16
