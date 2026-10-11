module

public import Tengoku.AddCombi.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Tengoku

open scoped ComplexConjugate Indicator

public section

namespace Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

/--
@isnad1 id=eq.0h4v.s6.90100b58a9f3 from=translated src=- shape=9a7e4d9c vocab=8342587b
-/
@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [indicator_apply]

/--
@isnad1 id=eq.0h3v.s7.b8bbb48cb3b3 from=translated src=- shape=31e2a87c vocab=8342587b
-/
@[local simp] lemma conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end Set
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
