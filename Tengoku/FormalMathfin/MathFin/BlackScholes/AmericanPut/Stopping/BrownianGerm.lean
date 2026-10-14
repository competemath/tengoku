/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel
public import Tengoku

/-! # Arbitrarily early downward Brownian excursions

Normalized evaluations at times `(n+1)⁻²` all have the standard Gaussian law.
Their negative limsup event belongs to the Brownian germ sigma algebra. The
zero-one law and bounded convergence show that this event has probability one.
No independence between these overlapping evaluations is claimed or needed.

## Result

Public entry points include `brownianProbeTime`, `brownianProbe`, `brownianNegativeGerm`, `brownianProbeTime_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The `n`-th probe time `(1/(n+1))^2`. -/
noncomputable def brownianProbeTime (n : ℕ) : ℝ≥0 := (1/((n : ℝ≥0)+1))^2

/--
@isnad1 id=lt.0h1v.s4.50e8d05c126e from=translated src=- shape=b9369acb vocab=5aa5027b
-/
theorem brownianProbeTime_pos (n : ℕ) : 0 < brownianProbeTime n := by
  unfold brownianProbeTime
  positivity

/--
@isnad1 id=tendsto.0h0v.s4.0d5e91d0deba from=translated src=- shape=8e2810f0 vocab=aafa5b43
-/
theorem brownianProbeTime_tendsto : Tendsto brownianProbeTime atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1/((n : ℝ≥0)+1))^2) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).pow 2

/-- The continuous test function `max 0 (min 1 (-x-1))`, valued in `[0,1]` and zero on
`-1 ≤ x`. -/
noncomputable def negativeProbeTest (x : ℝ) : ℝ := max 0 (min 1 (-x-1))

/--
@isnad1 id=continuo.0h0v.s3.41d132a293df from=translated src=- shape=e3d48bcb vocab=e25ca8c8
-/
theorem negativeProbeTest_continuous : Continuous negativeProbeTest := by
  unfold negativeProbeTest
  fun_prop

/--
@isnad1 id=and.0h1v.s4.ec4b662b4c0a from=translated src=- shape=fd7c5cb5 vocab=0f8573e0
-/
theorem negativeProbeTest_bounds (x : ℝ) : 0 ≤ negativeProbeTest x ∧ negativeProbeTest x ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

/--
@isnad1 id=eq.1h1v.s4.5d9d2f02b71c from=translated src=- shape=06880acc vocab=ed136e3d
-/
theorem negativeProbeTest_zero {x : ℝ} (hx : -1 ≤ x) : negativeProbeTest x = 0 := by
  unfold negativeProbeTest
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

/--
@isnad1 id=lt.0h0v.s5.e2c6e5de53f3 from=translated src=- shape=eb92cffe vocab=0673952e
-/
theorem negativeProbeTest_integral_pos : 0 < ∫ x, negativeProbeTest x ∂gaussianReal 0 1 := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  have hi : Integrable negativeProbeTest (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono_nonneg negativeProbeTest_continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => (negativeProbeTest_bounds x).1))
      (Eventually.of_forall (fun x => (negativeProbeTest_bounds x).2))
  apply integral_pos_of_integrable_nonneg_nonzero negativeProbeTest_continuous hi
    (fun x => (negativeProbeTest_bounds x).1)
  show negativeProbeTest (-2) ≠ 0
  norm_num [negativeProbeTest]

end MathFin.BlackScholes.AmericanPut.Stopping
