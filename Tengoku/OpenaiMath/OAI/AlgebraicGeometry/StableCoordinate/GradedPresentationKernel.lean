import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.ReesCoefficientCriterion
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.WeightedInitialKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# Kernel of the polynomial map to a principal weighted associated graded algebra

The proof connects three concrete calculations:
* coefficientwise vanishing in the Rees special fiber;
* the exact lower-representative criterion for a homogeneous polynomial;
* degreewise membership in a homogeneous principal ideal.

No associated-graded domain assumption or unproved initial-ideal identification
is used in this kernel computation.
-/

noncomputable section

namespace StableCoordinate.GradedPresentationKernel

open MvPolynomial WeightedInitial

variable {k σ A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Top components generate a homogeneous principal ideal, including for
arbitrary integer weights. -/
theorem top_principal_mem_iff (w : σ → ℤ) (H p : MvPolynomial σ k) (e : ℤ) :
    p ∈ Ideal.span ({weightedHomogeneousComponent w e H} : Set (MvPolynomial σ k)) ↔
      ∀ d : ℤ, weightedHomogeneousComponent w d p ∈
        Ideal.span ({weightedHomogeneousComponent w e H} : Set (MvPolynomial σ k)) := by
  let := weightedGradedAlgebra k w
  apply mem_iff_weightedHomogeneousComponent_mem
  apply Ideal.homogeneous_span
  intro q hq
  have hq' : q = weightedHomogeneousComponent w e H := Set.mem_singleton_iff.mp hq
  subst q
  exact ⟨e, weightedHomogeneousComponent_isWeightedHomogeneous e H⟩

end StableCoordinate.GradedPresentationKernel

end

end OAI
