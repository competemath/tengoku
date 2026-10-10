module

public import Tengoku

@[expose] public section

/--
@isnad1 id=eq.0h3v.s6.9a171ff6f670 from=translated src=- shape=b5450d3f vocab=e9517a4a
-/
lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a
