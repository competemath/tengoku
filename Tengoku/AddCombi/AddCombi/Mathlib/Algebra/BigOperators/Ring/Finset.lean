module

public import Tengoku.AddCombi.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Tengoku

open scoped Indicator

public section

namespace Finset
variable {α R : Type*} [Fintype α] [Semiring R]

/--
@isnad1 id=eq.0h3v.s6.683b34d76276 from=translated src=- shape=88b618bc vocab=72fb45bd
-/
@[simp] lemma sum_indicator_one (s : Finset α) : ∑ x, 𝟭_[(s : Set α), R] x = #s := by
  classical simp [Set.indicator_apply]

/--
@isnad1 id=eq.0h2v.s5.10040597d9f3 from=translated src=- shape=72270a66 vocab=ac430689
-/
lemma card_eq_sum_indicator_one (s : Finset α) : #s = ∑ x, 𝟭_[(s : Set α)] x :=
  (sum_indicator_one _).symm

end Finset
