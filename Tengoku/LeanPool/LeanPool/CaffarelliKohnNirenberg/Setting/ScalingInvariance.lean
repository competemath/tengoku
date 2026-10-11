/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceWeak
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS2
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS3S4
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling

/-!
# Scaling Invariance

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-- Space-time homeomorphism implementing positive parabolic scaling and translation. -/
def scalingHomeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
      (Homeomorph.addLeft z₀.2))

/-- Spatial dilation and translation as a homeomorphism. -/
def spatialHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

/-- Quadratic time dilation and translation as a homeomorphism. -/
def temporalHomeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    ℝ ≃ₜ ℝ :=
  (Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
    (Homeomorph.addLeft t₀)

end CKN
