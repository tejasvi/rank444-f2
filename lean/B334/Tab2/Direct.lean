import B334.Tab2.Deg
import B334.Tab2.Data
import B334.Bind.Row44Final
import B334.MethodK.Rows.R1
import B334.MethodK.Rows.R2
import B334.MethodK.Rows.R3
import B334.MethodK.Rows.R4
import B334.MethodK.Rows.R5
import B334.MethodK.Rows.R7
import B334.MethodK.Rows.R8
import B334.MethodK.Rows.R10
import B334.MethodK.Rows.R11
import B334.MethodK.Rows.R14
import B334.MethodK.Rows.R15
import B334.MethodK.Rows.R18
import B334.MethodK.Rows.R21
import B334.MethodK.Rows.R24
import B334.MethodK.Rows.R29
import B334.MethodK.Rows.R32
import B334.MethodK.Rows.R56
import B334.MethodK.Rows.R6
import B334.MethodK.Rows.R12
import B334.MethodK.Rows.R13
import B334.MethodK.Rows.R16
import B334.MethodK.Rows.R17
import B334.MethodK.Rows.R23
import B334.MethodK.Rows.R26
import B334.MethodK.Rows.R28
import B334.MethodK.Rows.R33
import B334.MethodK.Rows.R35
import B334.MethodK.Rows.R37
import B334.MethodK.Rows.R38
import B334.MethodK.Rows.R41
import B334.MethodK.Rows.R42
import B334.MethodK.Rows.R45
import B334.MethodK.Rows.R52
import B334.MethodK.Rows.R54
import B334.MethodK.Rows.R55
import B334.MethodK.Rows.R65
import B334.MethodK.Rows.R135
import B334.MethodK.Rows.R147

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The class-table rows certified directly (flattening, method K, the coset count of row 44)

GENERATED list; the facts are kernel checks that `basisOf c` is the certified row's basis and `lbOf c` is at most its
bound. Class 0 is the whole space (bound 0). -/

namespace B334.Tab2

open B334

theorem rowValid_zero (B : List ℕ) : RowValid B 0 := fun _ _ _ _ _ => Nat.zero_le _

theorem rowValid_of (c : ℕ) {B : List ℕ} {lb : ℕ} (hB : basisOf c = B) (hlb : lbOf c ≤ lb) (h : RowValid B lb) :
    RowValid (basisOf c) (lbOf c) := by
  rw [hB]; exact quotLB_le hlb h

theorem direct_0 : RowValid (basisOf 0) (lbOf 0) := by
  rw [show lbOf 0 = 0 by decide]; exact rowValid_zero _
theorem direct_1 : RowValid (basisOf 1) (lbOf 1) :=
  rowValid_of 1 (by decide) (by decide) B334.MethodK.R1.row
theorem direct_2 : RowValid (basisOf 2) (lbOf 2) :=
  rowValid_of 2 (by decide) (by decide) B334.MethodK.R2.row
theorem direct_3 : RowValid (basisOf 3) (lbOf 3) :=
  rowValid_of 3 (by decide) (by decide) B334.MethodK.R3.row
theorem direct_4 : RowValid (basisOf 4) (lbOf 4) :=
  rowValid_of 4 (by decide) (by decide) B334.MethodK.R4.row
theorem direct_5 : RowValid (basisOf 5) (lbOf 5) :=
  rowValid_of 5 (by decide) (by decide) B334.MethodK.R5.row
theorem direct_7 : RowValid (basisOf 7) (lbOf 7) :=
  rowValid_of 7 (by decide) (by decide) B334.MethodK.R7.row
theorem direct_8 : RowValid (basisOf 8) (lbOf 8) :=
  rowValid_of 8 (by decide) (by decide) B334.MethodK.R8.row
theorem direct_10 : RowValid (basisOf 10) (lbOf 10) :=
  rowValid_of 10 (by decide) (by decide) B334.MethodK.R10.row
theorem direct_11 : RowValid (basisOf 11) (lbOf 11) :=
  rowValid_of 11 (by decide) (by decide) B334.MethodK.R11.row
theorem direct_14 : RowValid (basisOf 14) (lbOf 14) :=
  rowValid_of 14 (by decide) (by decide) B334.MethodK.R14.row
theorem direct_15 : RowValid (basisOf 15) (lbOf 15) :=
  rowValid_of 15 (by decide) (by decide) B334.MethodK.R15.row
theorem direct_18 : RowValid (basisOf 18) (lbOf 18) :=
  rowValid_of 18 (by decide) (by decide) B334.MethodK.R18.row
theorem direct_21 : RowValid (basisOf 21) (lbOf 21) :=
  rowValid_of 21 (by decide) (by decide) B334.MethodK.R21.row
theorem direct_24 : RowValid (basisOf 24) (lbOf 24) :=
  rowValid_of 24 (by decide) (by decide) B334.MethodK.R24.row
theorem direct_29 : RowValid (basisOf 29) (lbOf 29) :=
  rowValid_of 29 (by decide) (by decide) B334.MethodK.R29.row
theorem direct_32 : RowValid (basisOf 32) (lbOf 32) :=
  rowValid_of 32 (by decide) (by decide) B334.MethodK.R32.row
theorem direct_56 : RowValid (basisOf 56) (lbOf 56) :=
  rowValid_of 56 (by decide) (by decide) B334.MethodK.R56.row
theorem direct_6 : RowValid (basisOf 6) (lbOf 6) :=
  rowValid_of 6 (by decide) (by decide) B334.MethodK.R6.row
theorem direct_12 : RowValid (basisOf 12) (lbOf 12) :=
  rowValid_of 12 (by decide) (by decide) B334.MethodK.R12.row
theorem direct_13 : RowValid (basisOf 13) (lbOf 13) :=
  rowValid_of 13 (by decide) (by decide) B334.MethodK.R13.row
theorem direct_16 : RowValid (basisOf 16) (lbOf 16) :=
  rowValid_of 16 (by decide) (by decide) B334.MethodK.R16.row
theorem direct_17 : RowValid (basisOf 17) (lbOf 17) :=
  rowValid_of 17 (by decide) (by decide) B334.MethodK.R17.row
theorem direct_23 : RowValid (basisOf 23) (lbOf 23) :=
  rowValid_of 23 (by decide) (by decide) B334.MethodK.R23.row
theorem direct_26 : RowValid (basisOf 26) (lbOf 26) :=
  rowValid_of 26 (by decide) (by decide) B334.MethodK.R26.row
theorem direct_28 : RowValid (basisOf 28) (lbOf 28) :=
  rowValid_of 28 (by decide) (by decide) B334.MethodK.R28.row
theorem direct_33 : RowValid (basisOf 33) (lbOf 33) :=
  rowValid_of 33 (by decide) (by decide) B334.MethodK.R33.row
theorem direct_35 : RowValid (basisOf 35) (lbOf 35) :=
  rowValid_of 35 (by decide) (by decide) B334.MethodK.R35.row
theorem direct_37 : RowValid (basisOf 37) (lbOf 37) :=
  rowValid_of 37 (by decide) (by decide) B334.MethodK.R37.row
theorem direct_38 : RowValid (basisOf 38) (lbOf 38) :=
  rowValid_of 38 (by decide) (by decide) B334.MethodK.R38.row
theorem direct_41 : RowValid (basisOf 41) (lbOf 41) :=
  rowValid_of 41 (by decide) (by decide) B334.MethodK.R41.row
theorem direct_42 : RowValid (basisOf 42) (lbOf 42) :=
  rowValid_of 42 (by decide) (by decide) B334.MethodK.R42.row
theorem direct_45 : RowValid (basisOf 45) (lbOf 45) :=
  rowValid_of 45 (by decide) (by decide) B334.MethodK.R45.row
theorem direct_52 : RowValid (basisOf 52) (lbOf 52) :=
  rowValid_of 52 (by decide) (by decide) B334.MethodK.R52.row
theorem direct_54 : RowValid (basisOf 54) (lbOf 54) :=
  rowValid_of 54 (by decide) (by decide) B334.MethodK.R54.row
theorem direct_55 : RowValid (basisOf 55) (lbOf 55) :=
  rowValid_of 55 (by decide) (by decide) B334.MethodK.R55.row
theorem direct_65 : RowValid (basisOf 65) (lbOf 65) :=
  rowValid_of 65 (by decide) (by decide) B334.MethodK.R65.row
theorem direct_135 : RowValid (basisOf 135) (lbOf 135) :=
  rowValid_of 135 (by decide) (by decide) B334.MethodK.R135.row
theorem direct_147 : RowValid (basisOf 147) (lbOf 147) :=
  rowValid_of 147 (by decide) (by decide) B334.MethodK.R147.row
theorem direct_44 : RowValid (basisOf 44) (lbOf 44) :=
  rowValid_of 44 (by decide) (by decide) B334.Row44.row

/-- the classes with a direct certificate -/
def directL : List ℕ := [0, 44, 1, 2, 3, 4, 5, 7, 8, 10, 11, 14, 15, 18, 21, 24, 29, 32, 56, 6, 12, 13, 16, 17, 23, 26, 28, 33, 35, 37, 38, 41, 42, 45, 52, 54, 55, 65, 135, 147]

theorem direct_ok : ∀ c ∈ directL, RowValid (basisOf c) (lbOf c) := by
  intro c hc
  simp only [directL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact direct_0
  · exact direct_44
  · exact direct_1
  · exact direct_2
  · exact direct_3
  · exact direct_4
  · exact direct_5
  · exact direct_7
  · exact direct_8
  · exact direct_10
  · exact direct_11
  · exact direct_14
  · exact direct_15
  · exact direct_18
  · exact direct_21
  · exact direct_24
  · exact direct_29
  · exact direct_32
  · exact direct_56
  · exact direct_6
  · exact direct_12
  · exact direct_13
  · exact direct_16
  · exact direct_17
  · exact direct_23
  · exact direct_26
  · exact direct_28
  · exact direct_33
  · exact direct_35
  · exact direct_37
  · exact direct_38
  · exact direct_41
  · exact direct_42
  · exact direct_45
  · exact direct_52
  · exact direct_54
  · exact direct_55
  · exact direct_65
  · exact direct_135
  · exact direct_147

end B334.Tab2
