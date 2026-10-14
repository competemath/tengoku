/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import Tengoku

/-!
# The parabolic Hardy--Littlewood maximal function

This file defines the uncentred maximal function using the genuine parabolic
metric from `Basic`.  The weak estimate is proved by the Vitali covering
theorem.  The covering argument follows the general metric-measure argument in
`Carleson/ToMathlib/HardyLittlewood.lean` from the Carleson project, released
under Apache 2.0.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Parabolic metric-ball family used by the maximal operator. -/
abbrev hardyLittlewoodParabolicMetricBall (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r

/-- Uncentered Hardy–Littlewood maximal function over parabolic balls. -/
def parabolicMaximalFunction (f : ParabolicPoint → ℝ≥0∞) (z : ParabolicPoint) : ℝ≥0∞ :=
  ⨆ c : ParabolicPoint, ⨆ r : ℝ,
    (hardyLittlewoodParabolicMetricBall c r).indicator
      (fun _ ↦ ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume) z

/--
@isnad1 id=le.1h4v.s5.b03b35386428 from=translated src=- shape=e4f74e44 vocab=665a9e58
-/
theorem parabolicMaximalFunction_average_le {f : ParabolicPoint → ℝ≥0∞}
    {c z : ParabolicPoint} {r : ℝ} (hz : z ∈ hardyLittlewoodParabolicMetricBall c r) :
    ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume ≤ parabolicMaximalFunction f z := by
  apply le_iSup₂_of_le c r
  simp only [indicator_of_mem hz]
  exact le_rfl

/-- Parabolic balls of bounded positive radius with average above a chosen level. -/
def parabolicMaximalLevelBalls (f : ParabolicPoint → ℝ≥0∞)
    (l : ℝ≥0∞) (n : ℕ) : Set (ParabolicPoint × ℝ) :=
  {i | 0 < i.2 ∧ i.2 ≤ (n : ℝ) ∧
    l < ⨍⁻ y in hardyLittlewoodParabolicMetricBall i.1 i.2, f y ∂volume}

end CKN.Foundation.Parabolic
