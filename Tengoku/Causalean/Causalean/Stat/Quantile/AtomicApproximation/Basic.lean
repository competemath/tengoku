module
public import Tengoku.Causalean.Causalean.Stat.Quantile.FiniteMassTransport

/-!
# Integrated CDF distance and equally weighted atomic measures

This module fixes the metric and atomic-measure conventions used by the synchronized
rational approximation theorem. Measures are finite Borel measures on the real line.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [The integrated-CDF distance](goal) between [a measure μ](hyp:μ) [and a
measure ν](hyp:ν) on the real line, over [the interval from a to
b](hyp:a,b), is [the absolute gap between their total masses plus the
integral from a to b of the absolute gap between their cumulative
distribution functions](step:1). -/
def cdfDistance (a b : ℝ) (μ ν : Measure ℝ) : ℝ :=
  |μ.real Set.univ - ν.real Set.univ| +
    ∫ t in a..b, |μ.real (Set.Iic t) - ν.real (Set.Iic t)|

/-- [The equally weighted atomic measure](goal) with [N atoms](hyp:N) [of
total weight w](hyp:w) [at locations x_1, …, x_N](hyp:x) is [the sum of
the point masses at the locations, each with weight w/N (read as zero when
w is negative)](step:1). -/
def equalAtomMeasure (N : ℕ) (w : ℝ) (x : Fin N → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (w / N) • Measure.dirac (x i)

/-- Over [an interval whose endpoints satisfy a ≤ b](hyp:a,b,hab), [the
integrated-CDF distance between finite measures on the real line satisfies
the triangle inequality](goal).
@isnad1 id=le.1h5v.s5.3ec0a1225ebf from=translated src=- shape=88a9808b vocab=e19ae730
-/
theorem cdfDistance_triangle (a b : ℝ) (hab : a ≤ b)
    (μ ν ξ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    cdfDistance a b μ ξ ≤ cdfDistance a b μ ν + cdfDistance a b ν ξ := by
  /- Use the real absolute-value triangle inequality pointwise, then monotonicity
     of the interval integral. The CDFs are interval integrable by
     `FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub`. -/
  let μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩
  let νf : FiniteMeasure ℝ := ⟨ν, inferInstance⟩
  let ξf : FiniteMeasure ℝ := ⟨ξ, inferInstance⟩
  have hμξ := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf ξf a b
  have hμν := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  have hνξ := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    νf ξf a b
  change IntervalIntegrable (fun t : ℝ => |μ.real (Iic t) - ξ.real (Iic t)|)
    volume a b at hμξ
  change IntervalIntegrable (fun t : ℝ => |μ.real (Iic t) - ν.real (Iic t)|)
    volume a b at hμν
  change IntervalIntegrable (fun t : ℝ => |ν.real (Iic t) - ξ.real (Iic t)|)
    volume a b at hνξ
  have hsum := hμν.add hνξ
  have hint : (∫ t in a..b, |μ.real (Iic t) - ξ.real (Iic t)|) ≤
      (∫ t in a..b, |μ.real (Iic t) - ν.real (Iic t)|) +
      (∫ t in a..b, |ν.real (Iic t) - ξ.real (Iic t)|) := by
    rw [← intervalIntegral.integral_add hμν hνξ]
    apply intervalIntegral.integral_mono_on hab hμξ hsum
    intro t _
    exact abs_sub_le _ _ _
  unfold cdfDistance
  have hmass := abs_sub_le (μ.real univ) (ν.real univ) (ξ.real univ)
  linarith

end Causalean.Stat.Quantile.AtomicApproximation
