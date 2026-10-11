module

public import Tengoku

public section

namespace NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

/--
@isnad1 id=eq.1h3v.s6.71da7a53c28f from=translated src=- shape=25d84600 vocab=a012ddde
-/
@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat
