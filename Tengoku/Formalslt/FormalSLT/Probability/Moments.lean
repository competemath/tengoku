import Tengoku

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace FormalSLT.Probability.Moments

noncomputable section

/--
Variance of a finite sum, covariance-expansion form.

This is a claim-facing wrapper around mathlib's
`ProbabilityTheory.variance_fun_sum'`.
Claim-facing wrapper for theorempath.com evidence entry `claim:expectation-variance-covariance-moments::variance-of-sum`.
@isnad1 id=eq.1h5v.s7.6c4cb66b4251 from=translated src=- shape=86c0e2fb vocab=e81526cf
-/
theorem varianceOfFiniteSumWithCovariance
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] =
      ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ] :=
  ProbabilityTheory.variance_fun_sum' hX

/--
Variance of a finite sum under pairwise zero covariance.

This proves the uncorrelated-variable reduction used by the page theorem.
@isnad1 id=eq.2h5v.s7.cbeda00cfe28 from=translated src=- shape=03ce92ee vocab=e81526cf
-/
theorem varianceOfFiniteSumPairwiseUncorrelated
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hCovZero :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] = ∑ i ∈ s, Var[X i; μ] := by
  rw [varianceOfFiniteSumWithCovariance hX]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · exact ProbabilityTheory.covariance_self (hX i hi).aemeasurable
  · intro j hj hji
    exact hCovZero i hi j hj hji.symm
  · intro hiNot
    exact (hiNot hi).elim

/--
Law of total variance.

This is an exact claim-facing wrapper around mathlib's conditional-variance
decomposition `ProbabilityTheory.integral_condVar_add_variance_condExp`.
Claim-facing wrapper for theorempath.com evidence entry `claim:expectation-variance-covariance-moments::law-of-total-variance`.
@isnad1 id=eq.2h5v.s7.73049d996e58 from=translated src=- shape=08ffa310 vocab=8824dc6f
-/
theorem lawOfTotalVariance
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] :=
  ProbabilityTheory.integral_condVar_add_variance_condExp hm hX

end

end FormalSLT.Probability.Moments
