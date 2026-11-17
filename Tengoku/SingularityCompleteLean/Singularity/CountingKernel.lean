import Tengoku.SingularityCompleteLean.Singularity.CountingSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absolutely convergent kernel expansions on counting L²

A bounded operator acts by its matrix coefficients against an L² vector. The
series is absolutely convergent by the L² inner-product integrability theorem.
This supplies infinite entrance-boundary sums without interchanging an
uncontrolled matrix double sum.
-/

noncomputable section
open MeasureTheory
namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

omit [Countable X] in
/-- Counting L² inner products are absolutely summable coordinate products.
@isnad1 id=summable.0h3v.s9.c59a136ac021 from=translated src=- shape=864fae6c vocab=1a691d9f
-/
theorem counting_inner_summable (f g : GroupL2 X) :
    Summable (fun x => inner ℂ (f x) (g x)) :=
  (integrable_count_iff.mp (L2.integrable_inner (𝕜 := ℂ) f g)).of_norm

/-- Exact coordinate formula for the counting L² inner product.
@isnad1 id=eq.0h3v.s10.939b309d070e from=translated src=- shape=9fbe2777 vocab=f7688975
-/
theorem counting_inner_eq_tsum (f g : GroupL2 X) :
    inner ℂ f g = ∑' x, inner ℂ (f x) (g x) := by
  rw [L2.inner_def]
  simpa [measureReal_def] using integral_countable (L2.integrable_inner (𝕜 := ℂ) f g)

omit [Countable X] in
/-- An adjoint point-mass column is the conjugate matrix row.
@isnad1 id=eq.0h4v.s16.c732524100fb from=translated src=- shape=c8eb6149 vocab=c07fb145
-/
theorem counting_adjoint_coefficient (T : GroupL2 X →L[ℂ] GroupL2 X) (x y : X) :
    T.adjoint (countingDelta x) y = (starRingEnd ℂ) (T (countingDelta y) x) := by
  rw [← countingDelta_inner y, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, countingDelta_inner]

omit [Countable X] in
/-- Every scalar matrix row acts by an absolutely convergent series.
@isnad1 id=summable.0h4v.s13.62f5a4dcb7dd from=translated src=- shape=9a24042d vocab=4301bb94
-/
theorem counting_operator_kernel_summable (T : GroupL2 X →L[ℂ] GroupL2 X) (f : GroupL2 X) (x : X) :
    Summable (fun y => T (countingDelta y) x * f y) := by
  have hh := counting_inner_summable (T.adjoint (countingDelta x)) f
  simpa [counting_adjoint_coefficient, RCLike.inner_apply, mul_comm] using hh

/-- The matrix series equals the actual bounded-operator value.
@isnad1 id=eq.0h4v.s13.5cd1d097faab from=translated src=- shape=ae328781 vocab=1af999c5
-/
theorem counting_operator_eq_tsum (T : GroupL2 X →L[ℂ] GroupL2 X) (f : GroupL2 X) (x : X) :
    T f x = ∑' y, T (countingDelta y) x * f y := by
  rw [← countingDelta_inner x, ← ContinuousLinearMap.adjoint_inner_left, counting_inner_eq_tsum]
  simp [counting_adjoint_coefficient, RCLike.inner_apply, mul_comm]

omit [Countable X] in
/-- Restricting a point mass retains it precisely when its point is in A.
@isnad1 id=eq.0h3v.s14.68ab5778f2c0 from=translated src=- shape=ea08529a vocab=caad684f
-/
theorem supportedRestriction_delta_mem (A : Set X) (a : A) :
    supportedRestriction A (countingDelta (a : X)) = supportedDelta A a := by
  exact supportedRestriction_inclusion A (supportedDelta A a)

omit [Countable X] in
/--
@isnad1 id=eq.1h3v.s14.9421950a5eb0 from=translated src=- shape=b5ff35fa vocab=2af32a73
-/
theorem supportedRestriction_delta_notMem (A : Set X) (y : X) (hy : y ∉ A) :
    supportedRestriction A (countingDelta y) = 0 := by
  apply Subtype.ext
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  have hz : (0 : GroupL2 X) x = 0 := by
    simpa only [countingEvaluation_apply] using (countingEvaluation x).map_zero
  change ((supportedRestriction A (countingDelta y)) : GroupL2 X) x = (0 : GroupL2 X) x
  rw [hz]
  by_cases hx : x ∈ A
  · rw [supportedRestriction_apply A _ ⟨x, hx⟩, countingDelta_apply]
    simp only [ite_eq_right_iff]
    intro he
    exact (hy (he ▸ hx)).elim
  · exact (supportedRestriction A (countingDelta y)).property x hx

end Singularity
