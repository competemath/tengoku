import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive C*-square roots commute with genuine star-algebra maps -/

noncomputable section
set_option autoImplicit false
namespace StarAlgHom
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A genuine unital complex star-algebra map preserves the positive
C*-square root, by positivity and uniqueness.
@isnad1 id=eq.1h4v.s9.d7a590db767b from=translated src=- shape=8a864018 vocab=4b473c2e
-/
theorem map_sqrt (φ : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) :
    φ (CFC.sqrt a) = CFC.sqrt (φ a) := by
  symm
  apply CFC.sqrt_unique _ (map_nonneg φ (CFC.sqrt_nonneg a))
  rw [← map_mul, CFC.sqrt_mul_sqrt_self a ha]

end StarAlgHom
