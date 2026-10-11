/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls

/-!
# Morrey Form

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Parabolic.Integration
noncomputable section
namespace CKN
/-- Pressure coefficient controlling the small-scale Morrey integral bounds. -/
def pressureSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 :
  ℝ))
/-- Gradient coefficient controlling the small-scale Morrey integral bounds. -/
def gradientSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ))
/-- Velocity coefficient obtained from Sobolev interpolation in the small-scale Morrey estimate.
-/
def velocitySmallConstant (M : ℝ) : ℝ≥0∞ := ((ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
    localSobolevConstant ^ (3 / 2 : ℝ)) * ENNReal.ofReal (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * (4 : ℝ) ^ (16
        / 5 : ℝ))
/-! The Step 2 decay certificate is converted into the three Morrey bounds. -/
end CKN
