/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Maximal.HardyLittlewood
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.LayerCake
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.WeightedKernelIdentity
public import Tengoku

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

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Explicit strong-type coefficient for the Euclidean maximal operator. -/
def maximalStrongConstant (p : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (5 ^ 3) * ENNReal.ofReal p /
    ENNReal.ofReal (p - 1)

/-- Metric-ball family used in the maximal operator's strong-type estimate. -/
abbrev strongTypeMetricBall (z : Vec3) (r : ℝ) : Set Vec3 :=
  Metric.ball z r

/-- Part of an extended nonnegative function strictly above a truncation level. -/
def highPart (f : Vec3 → ℝ≥0∞) (a : ℝ≥0∞) :
    Vec3 → ℝ≥0∞ := {z | a < f z}.indicator f

/-- Part of an extended nonnegative function at or below a truncation level. -/
def lowPart (f : Vec3 → ℝ≥0∞) (a : ℝ≥0∞) :
    Vec3 → ℝ≥0∞ := {z | f z ≤ a}.indicator f

/-- The weight `t ^ (p - 2)` on positive inputs, extended by zero elsewhere. -/
def positiveRpow (p t : ℝ) : ℝ :=
  if 0 < t then Real.exp ((p - 2) * Real.log t) else 0

/-- Weighted upper-tail integrand in the strong-type maximal-function estimate. -/
def weightedTailIntegrand (f : Vec3 → ℝ≥0∞) (p : ℝ)
    (t : ℝ) (z : Vec3) : ℝ≥0∞ :=
  ENNReal.ofReal (positiveRpow p t) *
    ({z | ENNReal.ofReal (t / 2) < f z}.indicator f) z

/--
@isnad1 id=le.0h2v.s6.c71b3c4e9c79 from=translated src=- shape=7c255b2f vocab=c98e6f25
-/
theorem maximalFunction_le_essSup
    (f : Vec3 → ℝ≥0∞) (z : Vec3) :
    maximalFunction f z ≤ essSup f volume := by
  rw [maximalFunction]
  refine iSup_le fun c ↦ iSup_le fun r ↦ ?_
  by_cases hz : z ∈ strongTypeMetricBall c r
  · simp only [indicator_of_mem hz]
    exact setLAverage_le_essSup (strongTypeMetricBall c r) f
  · simp only [indicator_of_notMem hz, zero_le]

end CKN.Foundation.Euclidean
