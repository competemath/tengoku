/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.NormalizedExponential
public import Tengoku.LeanPool.LeanPool.Feige.SimplexMeasure
import Tengoku.LeanPool.LeanPool.Feige.NormalizedExponentialProbability
public import Tengoku

/-!
# Uniform simplex law from normalized exponentials

This module identifies the factorial-density simplex measure obtained by
the normalized-exponential calculation with the project's existing uniform
simplex probability measure.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set

namespace Feige

variable {n : ℕ}

/--
@isnad1 id=eq.0h1v.s4.b8c736cfee8f from=translated src=- shape=6dea8734 vocab=c0ad6f20
-/
theorem normalizedExponentialSimplexMeasure_eq_uniform :
    normalizedExponentialSimplexMeasure (n := n) =
      simplexUniformMeasure (Fin n) := by
  unfold normalizedExponentialSimplexMeasure simplexUniformMeasure
    simplexRestrictedVolume
  rw [volume_fullSimplex_eq_factorial_inv (n := n)]
  rw [inv_inv]

/-- The normalized-coordinate map on real product coordinates. -/
noncomputable def normalizedExponentialCoordinates
    (e : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  (exponentialSimplexInverse e).2

/-- Independent unit exponentials on the positive real orthant, written as
an absolutely continuous measure in real product coordinates. -/
noncomputable def realExponentialProductMeasure :
    Measure (ℝ × (Fin n → ℝ)) :=
  (volume.restrict (positiveExponentialOrthant (n := n))).withDensity
    (fun e ↦ ENNReal.ofReal (Real.exp (-exponentialTotal e)))

/--
@isnad1 id=eq.1h2v.s6.86167f48ea9b from=translated src=- shape=b0eb4ced vocab=ff4d7232
-/
theorem realExponentialProductMeasure_lintegral
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ e, h (normalizedExponentialCoordinates e)
        ∂(realExponentialProductMeasure (n := n)) =
      ∫⁻ x, h x ∂(simplexUniformMeasure (Fin n)) := by
  rw [realExponentialProductMeasure,
    lintegral_withDensity_eq_lintegral_mul]
  · change
      (∫⁻ e in positiveExponentialOrthant (n := n),
        ENNReal.ofReal (Real.exp (-exponentialTotal e)) *
          h (exponentialSimplexInverse e).2 ∂volume) = _
    rw [lintegral_normalizedExponential_eq_simplex h hh,
      normalizedExponentialSimplexMeasure_eq_uniform]
  · exact continuous_exponentialTotal.measurable.neg.exp.ennreal_ofReal
  · exact hh.comp measurable_exponentialSimplexInverse.snd

/--
@isnad1 id=measurab.0h1v.s5.20f3b48dff65 from=translated src=- shape=b23881e2 vocab=adc89d96
-/
theorem measurable_normalizedExponentialCoordinates :
    Measurable (normalizedExponentialCoordinates (n := n)) :=
  measurable_exponentialSimplexInverse.snd

/-- Measure-level pushforward form of the normalized exponential law.
@isnad1 id=eq.0h1v.s6.31d5cce85af1 from=translated src=- shape=032692b4 vocab=2d939682
-/
theorem map_realExponentialProductMeasure_normalizedCoordinates :
    Measure.map (normalizedExponentialCoordinates (n := n))
        (realExponentialProductMeasure (n := n)) =
      simplexUniformMeasure (Fin n) := by
  ext s hs
  have htest : Measurable
      (fun x : Fin n → ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) := by
    exact measurable_one.indicator hs
  have h := realExponentialProductMeasure_lintegral
    (n := n) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) htest
  rw [Measure.map_apply measurable_normalizedExponentialCoordinates hs]
  calc
    realExponentialProductMeasure (n := n)
        (normalizedExponentialCoordinates ⁻¹' s) =
      ∫⁻ e, (normalizedExponentialCoordinates ⁻¹' s).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) e
        ∂(realExponentialProductMeasure (n := n)) := by
          rw [lintegral_indicator
            (hs.preimage measurable_normalizedExponentialCoordinates)]
          simp
    _ = ∫⁻ e, s.indicator (fun _ ↦ (1 : ℝ≥0∞))
        (normalizedExponentialCoordinates e)
        ∂(realExponentialProductMeasure (n := n)) := by
          apply lintegral_congr
          intro e
          rfl
    _ = _ := by
      rw [lintegral_indicator hs] at h
      simpa using h

end Feige
