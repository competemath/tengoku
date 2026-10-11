import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.Conditioning

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def conditionalProbability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (ξ : E → Bool) : ℝ :=
  (ProductCylinder.law (fixedParameter p J ξ)).real C

omit [Countable E] in
theorem conditionalProbability_determined (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) :
    ProductCylinder.DeterminedBy J (conditionalProbability p J C) := by
  intro ω ω' h
  unfold conditionalProbability
  rw [fixedParameter_congr p J h]

end InfiniteConditioning

end OAI
