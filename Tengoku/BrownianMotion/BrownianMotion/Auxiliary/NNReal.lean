module

public import Tengoku

@[expose] public section

namespace NNReal

/--
@isnad1 id=eq.0h2v.s6.f78a56b7ef87 from=translated src=- shape=0f38d0c8 vocab=aea6d313
-/
lemma add_sub_two_mul_min_eq_max (s t : ℝ≥0) : s + t - 2 * min s t = max (s - t) (t - s) := by
  wlog hst : s ≤ t
  · convert this t s (le_of_not_ge hst) using 1
    · rw [add_comm, min_comm]
    · rw [max_comm]
  rw [min_eq_left hst, max_eq_right, two_mul, add_tsub_add_eq_tsub_left]
  grw [hst]

end NNReal
