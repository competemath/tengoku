/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# The Euclidean Hardy--Littlewood maximal function

This module defines the uncentred maximal function on `Vec3` and proves its
weak `(1,1)` estimate by the metric Vitali covering theorem.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Metric-ball family used by the Euclidean Hardy–Littlewood maximal operator. -/
abbrev hardyLittlewoodMetricBall (c : Vec3) (r : ℝ) : Set Vec3 := Metric.ball c r

/-- The uncentred Hardy--Littlewood maximal function on `Vec3`. -/
def maximalFunction (f : Vec3 → ℝ≥0∞) (z : Vec3) : ℝ≥0∞ :=
  ⨆ c : Vec3, ⨆ r : ℝ,
    (hardyLittlewoodMetricBall c r).indicator
      (fun _ ↦ ⨍⁻ y in hardyLittlewoodMetricBall c r, f y ∂volume) z

private lemma volume_metricBall (x : Vec3) {r : ℝ} (hr : 0 < r) :
    volume (hardyLittlewoodMetricBall x r) = ENNReal.ofReal ((2 * r) ^ 3) := by
  rw [MeasureTheory.volume_pi_ball x hr]
  simp only [Real.volume_ball, Finset.prod_const]
  norm_num [Fintype.card_fin]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  have hmul : ENNReal.ofReal 2 * ENNReal.ofReal r = ENNReal.ofReal (2 * r) :=
    (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [h2, hmul, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * r) 3]

/--
@isnad1 id=eq.1h2v.s7.a4a4fd1fcbe6 from=translated src=- shape=798daa44 vocab=1bc9ef5d
-/
theorem volume_metricBall_eq {x : Vec3} {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ 3) := by
  exact volume_metricBall x hr

/--
@isnad1 id=le.1h4v.s7.e3019ee5bd05 from=translated src=- shape=e4f74e44 vocab=b0d1d236
-/
theorem maximalFunction_average_le {f : Vec3 → ℝ≥0∞}
    {c z : Vec3} {r : ℝ} (hz : z ∈ hardyLittlewoodMetricBall c r) :
    ⨍⁻ y in hardyLittlewoodMetricBall c r, f y ∂volume ≤ maximalFunction f z := by
  apply le_iSup₂_of_le c r
  simp only [indicator_of_mem hz]
  exact le_rfl

/-- Positive-radius balls of bounded radius whose average exceeds the chosen level. -/
def maximalLevelBalls (f : Vec3 → ℝ≥0∞)
    (l : ℝ≥0∞) (n : ℕ) : Set (Vec3 × ℝ) :=
  {i | 0 < i.2 ∧ i.2 ≤ (n : ℝ) ∧
    l < ⨍⁻ y in hardyLittlewoodMetricBall i.1 i.2, f y ∂volume}

end CKN.Foundation.Euclidean
