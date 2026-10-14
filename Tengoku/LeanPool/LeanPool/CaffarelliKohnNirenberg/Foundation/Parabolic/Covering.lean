/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import Tengoku

/-!
# A parabolic Vitali covering estimate

This file records the measure estimate obtained by applying the Vitali
covering theorem to the metric balls associated with the parabolic cylinders.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Explicit parabolic metric-ball family used in the covering argument. -/
abbrev coveringParabolicMetricBall (c : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c r

/--
@isnad1 id=measurab.0h3v.s3.a995a987a623 from=translated src=- shape=448046c7 vocab=22c8ccfa
-/
lemma measurableSet_parabolicCylinder (x : Vec3) (t r : ℝ) :
    MeasurableSet (parabolicCylinder x t r) := by
  rw [parabolicCylinder]
  exact (vec3Ball_measurable x r).prod measurableSet_Ioc

/-- Volume coefficient for the parabolic covering estimates. -/
noncomputable def parabolicVolumeConstant : ℝ≥0∞ :=
  ENNReal.ofReal ((4 : ℝ) ^ 5) * volume (parabolicCylinder 0 0 1)

end CKN.Foundation.Parabolic
