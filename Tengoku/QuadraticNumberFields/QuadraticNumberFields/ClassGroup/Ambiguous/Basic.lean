/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Dynamics.FixedPoints.Basic
import Tengoku.Seed.RingTheory.Ideal.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ambiguous Ideals

This file contains the ideal-level fixedness predicate used in the ambiguous
class-group layer. For a ring automorphism `σ`, an ideal is ambiguous when
mapping it along `σ` fixes it.
-/
namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

section FixedIdeals

variable {B : Type*} [CommRing B]

/-- An ideal `I` is ambiguous with respect to a ring automorphism `σ` if `σ`
fixes `I`.-/
def IsAmbiguousIdeal (σ : B ≃+* B) (I : Ideal B) : Prop :=
  Ideal.map (σ : B →+* B) I = I

/-- Ambiguous ideals are exactly fixed points of the induced ideal map.
@isnad1 id=iff.0h3v.s7.b780d7afdef0 from=translated src=- shape=e8f80e7a vocab=2364ca6d
-/
theorem isAmbiguousIdeal_iff_isFixedPt (σ : B ≃+* B) (I : Ideal B) :
    IsAmbiguousIdeal σ I ↔ Function.IsFixedPt (Ideal.map (σ : B →+* B)) I :=
  Iff.rfl

/-- The top ideal is ambiguous.
@isnad1 id=isambigu.0h2v.s6.1a072d33c389 from=translated src=- shape=525248ea vocab=2eb73bb8
-/
@[simp]
theorem isAmbiguousIdeal_top (σ : B ≃+* B) : IsAmbiguousIdeal σ (⊤ : Ideal B) := by
  rw [IsAmbiguousIdeal, Ideal.map_top]

/-- The product of ambiguous ideals is ambiguous.
@isnad1 id=isambigu.2h4v.s7.2c61009e5ef2 from=translated src=- shape=01e30dd9 vocab=d53e2a8b
-/
theorem IsAmbiguousIdeal.mul {σ : B ≃+* B} {I J : Ideal B}
    (hI : IsAmbiguousIdeal σ I) (hJ : IsAmbiguousIdeal σ J) :
    IsAmbiguousIdeal σ (I * J) := by
  unfold IsAmbiguousIdeal at hI hJ ⊢
  rw [Ideal.map_mul, hI, hJ]

end FixedIdeals

end Ambiguous
end ClassGroup
end QuadraticNumberFields
