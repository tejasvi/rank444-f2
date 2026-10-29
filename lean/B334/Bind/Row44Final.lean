import B334.Bind.Row44
import B334.MethodK.Rows.R7
import B334.MethodK.Rows.R13
import B334.MethodK.Rows.R16

/-! # Row 44, final

`RowValid basis 18` for class 44, from `row44_of` and the three cited class rows: class 7 (lb 8, a flattening
certificate, f = 0), classes 13 and 16 (lb 16, method K). Their bases are `cb7`, `cb13` and `cb16` by definition (the
table's bases). -/

namespace B334.Row44

/-- **Row 44**: R(T334 mod span basis) ≥ 18. -/
theorem row : RowValid basis 18 :=
  row44_of B334.MethodK.R7.row B334.MethodK.R13.row B334.MethodK.R16.row

end B334.Row44
