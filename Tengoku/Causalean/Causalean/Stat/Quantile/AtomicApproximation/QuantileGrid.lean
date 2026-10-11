module
public import Tengoku.Causalean.Causalean.Stat.Quantile.AtomicApproximation.ProbabilityGrid

/-!
# Equal-weight quantile grids on compact intervals

This module isolates the measure-theoretic approximation before atom locations
are moved into a prescribed dense subset.
-/

public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [Two finite real measures](hyp:μ,ν), [an interval and error level](hyp:a,b,c),
[the interval endpoints ordered](hyp:hab), [equal total real masses](hyp:hmass), and [a uniform CDF-error
bound on the interval](hyp:hpoint) give [an integrated-CDF discrepancy bound by
interval length times that error level](goal). -/
theorem cdfDistance_le_of_pointwise_cdf_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b c : ℝ) (hab : a ≤ b)
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (hpoint : ∀ t ∈ Set.Icc a b,
      |μ.real (Set.Iic t) - ν.real (Set.Iic t)| ≤ c) :
    cdfDistance a b μ ν ≤ (b - a) * c := by
  /- Use `FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub` for the
     integrand and `intervalIntegral.integral_mono_on` against the constant
     function `c`. Rewrite `intervalIntegral.integral_const`, then eliminate
     the mass term with `hmass`. No positivity of the original mass is needed. -/
  let μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩
  let νf : FiniteMeasure ℝ := ⟨ν, inferInstance⟩
  have hint := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  change IntervalIntegrable
    (fun t : ℝ => |μ.real (Iic t) - ν.real (Iic t)|) volume a b at hint
  have hbound := intervalIntegral.integral_mono_on hab hint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a b)
    hpoint
  rw [intervalIntegral.integral_const] at hbound
  simpa [cdfDistance, hmass, smul_eq_mul, mul_comm] using hbound

end Causalean.Stat.Quantile.AtomicApproximation
