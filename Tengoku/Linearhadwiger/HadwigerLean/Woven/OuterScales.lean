import Tengoku.Linearhadwiger.HadwigerLean.Woven.CommonLemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer scales for the shared woven induction

With top scale `3^m`, the integer scales are `2^i * 3^(m-i)` for
`0 ≤ i ≤ m`. Successive scales satisfy `3 * child = 2 * parent`, so
the pair budget of the child is exactly twice the parent scale.
-/

namespace HadwigerLean

namespace Woven

/-- The `i`th integer scale below `3^m`.-/
def outerScale (m i : ℕ) : ℕ := 2 ^ i * 3 ^ (m - i)

/--
@isnad1 id=eq.0h1v.s4.dda33f9be6fd from=translated src=- shape=70073102 vocab=fa549146
-/
@[simp] theorem outerScale_zero (m : ℕ) : outerScale m 0 = 3 ^ m := by
  simp [outerScale]

/--
@isnad1 id=eq.0h1v.s4.329f332a1794 from=translated src=- shape=a371bd2e vocab=fa549146
-/
@[simp] theorem outerScale_last (m : ℕ) : outerScale m m = 2 ^ m := by
  simp [outerScale]

/--
@isnad1 id=lt.0h2v.s3.95c1686d0ea8 from=translated src=- shape=a120b2a8 vocab=899ec6af
-/
theorem outerScale_pos (m i : ℕ) : 0 < outerScale m i := by
  simp [outerScale]

/-- The exact integer child recurrence, with no rounding loss.
@isnad1 id=eq.1h2v.s5.d06d0bc142f5 from=translated src=- shape=997d52ea vocab=4e8297f0
-/
theorem outerScale_child (m i : ℕ) (hi : i < m) :
    3 * outerScale m (i + 1) = 2 * outerScale m i := by
  have hsub : m - i = (m - (i + 1)) + 1 := by omega
  simp only [outerScale, pow_succ]
  rw [hsub]
  simp only [pow_succ]
  ac_rfl

/-- The child at a nonfinal scale is smaller than its parent.
@isnad1 id=lt.1h2v.s4.266a83df141f from=translated src=- shape=ebe1bbe4 vocab=744d1759
-/
theorem outerScale_child_lt (m i : ℕ) (hi : i < m) :
    outerScale m (i + 1) < outerScale m i := by
  have hp := outerScale_pos m i
  have hc := outerScale_child m i hi
  omega

/-- The next scale's threefold path budget is the current scale's
twofold budget.
@isnad1 id=eq.1h2v.s5.d06d0bc142f5 from=translated src=- shape=997d52ea vocab=4e8297f0
-/
theorem outerScale_child_pair_budget (m i : ℕ) (hi : i < m) :
    3 * outerScale m (i + 1) = 2 * outerScale m i :=
  outerScale_child m i hi

end Woven

end HadwigerLean
