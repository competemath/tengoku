import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.GradedPresentationMap
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.GradedPresentationKernel
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.PrincipalInitialRelation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The actual associated graded presentation for the source hypersurface

This identifies the Rees special fiber of the source quotient filtration with
the exact degeneration ring `Obstruction.G`, with its independent generators.
-/

noncomputable section

namespace StableCoordinate.AssociatedGradedPresentation

open MvPolynomial Obstruction WeightedInitial Filtration GradedPresentationMap

/-- The two source-weight APIs describe precisely the same integer weight. -/
theorem monomialWeight_eq_weight :
    Filtration.monomialWeight = Finsupp.weight presentationWeight := by
  apply Finsupp.addHom_ext
  intro i n
  rw [Finsupp.weight_single]
  fin_cases i <;> simp [Filtration.monomialWeight, presentationWeight ]

variable (k : Type*) [CommRing k]

variable {k}
variable {A : Type*} [CommRing A] [Algebra k A]

/-- The coefficient of the actual source Rees map is the image of the matching
weighted homogeneous component. -/
theorem reesMap_coeff_weighted (φ : P k 5 →ₐ[k] A) (p : P k 5) (d : ℤ) :
    (reesMap φ p : LaurentPolynomial A).coeff d =
      φ (weightedHomogeneousComponent presentationWeight d p) := by
  classical
  rw [reesMap_coeff, weightedHomogeneousComponent_apply, Finset.sum_filter]
  simp only [monomialWeight_eq_weight]

variable (k)

/-- The actual polynomial presentation map of the source hypersurface. -/
abbrev quotientMap : P k 5 →ₐ[k] Obstruction.A k := Ideal.Quotient.mkₐ k (idealA k)

/-- The actual Rees associated graded algebra of the source image filtration. -/
abbrev associatedGraded := imageGr (quotientMap k)

/-- The actual polynomial map onto the source's associated graded algebra. -/
abbrev gradedPresentationMap : P k 5 →ₐ[k] associatedGraded k :=
  gradedMap (quotientMap k)

variable [IsDomain k]

end StableCoordinate.AssociatedGradedPresentation

end

end OAI
