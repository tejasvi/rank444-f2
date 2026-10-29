import B334.MethodK.Rows.R135D

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! # Method K, row 135: K-W chunk 60 of 64 (masks 3840 … 3903). GENERATED; do not edit. -/

namespace B334.MethodK.R135
open B334.MethodK B334.Core

theorem kW60 : B334.Core.allLT 64 (fun i => kwAt M0r Nr (4 * 8) Yz 12 16 false (60 * 64 + i)) = true := by
  decide +kernel

end B334.MethodK.R135
