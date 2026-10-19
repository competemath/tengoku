/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Adams

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adams Endpoints

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- A potential vanishes when its input vanishes almost everywhere. -/
theorem parabolicRieszPotential_eq_zero_of_ae_eq_zero
    {β : ℝ} {f : ParabolicPoint → ℝ} (hzero : f =ᵐ[volume] 0)
    (z : ParabolicPoint) :
    parabolicRieszPotential β f z = 0 := by
  unfold parabolicRieszPotential
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hzero] with w hw
  simp [hw]

/-- The near-field geometric constant is strictly positive. -/
theorem parabolicHedbergNearConstant_pos {β : ℝ} :
    0 < parabolicHedbergNearConstant β := by
  unfold parabolicHedbergNearConstant
  have hvol : 0 < volume (parabolicCylinder 0 0 1) :=
    Integration.volume_parabolicCylinder_pos (by norm_num)
  have hfactor : 0 < ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
    exact ENNReal.mul_pos (by positivity)
      (ENNReal.mul_pos (by positivity) hvol.ne').ne'
  have hterm : 0 < ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc 0 : ℝ)) ^ β) := by
    positivity
  have hsum : ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc 0 : ℝ)) ^ β) ≤
      ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) :=
    ENNReal.le_tsum (f := fun n : ℕ =>
      ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) 0
  exact ENNReal.mul_pos hfactor.ne' (lt_of_lt_of_le hterm hsum).ne'

end CKN.Foundation.Parabolic.Morrey
