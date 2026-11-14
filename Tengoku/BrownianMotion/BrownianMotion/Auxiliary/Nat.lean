module

public import Tengoku

@[expose] public section
namespace Tengoku.BrownianMotion end Tengoku.BrownianMotion open Tengoku.BrownianMotion 
/--
@isnad1 id=eq.0h3v.s6.9a171ff6f670 from=translated src=- shape=b5450d3f vocab=e9517a4a
-/
lemma _root_.Tengoku.BrownianMotion.pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a
-- Tengoku: root names of this library moved to Tengoku.BrownianMotion so they do not collide with other libraries (generated)
