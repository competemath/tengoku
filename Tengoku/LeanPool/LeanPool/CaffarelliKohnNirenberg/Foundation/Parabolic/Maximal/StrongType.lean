/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Maximal.HardyLittlewood
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.LayerCake
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.WeightedKernelIdentity

/-!
# Strong maximal estimates

This file records the direct layer-cake proof of the strong maximal estimate
from the weak estimate in `HardyLittlewood`.  The proof uses truncation at
half the level and Tonelli's theorem, so it does not depend on an abstract
interpolation package.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Explicit strong-type coefficient for the parabolic maximal operator. -/
def parabolicMaximalStrongConstant (p : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (10 ^ 5) * ENNReal.ofReal p /
    ENNReal.ofReal (p - 1)

/-- Parabolic ball family used in the strong-type maximal-function proof. -/
abbrev strongMetricBall (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r

/-- Part of a nonnegative parabolic source strictly above the truncation level. -/
def highPart (f : ParabolicPoint → ℝ≥0∞) (a : ℝ≥0∞) :
    ParabolicPoint → ℝ≥0∞ := {z | a < f z}.indicator f

/-- Part of a nonnegative parabolic source at or below the truncation level. -/
def lowPart (f : ParabolicPoint → ℝ≥0∞) (a : ℝ≥0∞) :
    ParabolicPoint → ℝ≥0∞ := {z | f z ≤ a}.indicator f

/-- Positive-time power weight for the maximal-function distribution integral. -/
def positiveRpow (p t : ℝ) : ℝ :=
  if 0 < t then Real.exp ((p - 2) * Real.log t) else 0

/-- Weighted upper-tail integrand in the parabolic maximal-function estimate. -/
def weightedTailIntegrand (f : ParabolicPoint → ℝ≥0∞) (p : ℝ)
    (t : ℝ) (z : ParabolicPoint) : ℝ≥0∞ :=
  ENNReal.ofReal (positiveRpow p t) *
    ({z | ENNReal.ofReal (t / 2) < f z}.indicator f) z

end CKN.Foundation.Parabolic
