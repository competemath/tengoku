/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku

/-!
# Local Sobolev and interpolation inequalities for smooth functions

This file proves local Sobolev and interpolation inequalities for smooth
functions. The corresponding weak H¹ estimate has the form

`‖u‖₆(Bᵣ) ≤ C (‖∇u‖₂(B₂ᵣ) + r⁻¹ ‖u‖₂(B₂ᵣ))`.

Passing from smooth functions to weak H¹ functions requires local approximation
of both the function and its gradient, together with the weak product rule
for a smooth cutoff. Interpolation yields the `L³` and `L^(10/3)` estimates;
for `Q_r = (t-r²,t) × B_r`, the `L³` cylinder factor is `r^(1/2)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CKN

noncomputable section

/-- The extended `Lᵖ` seminorm of a function on a measurable set. -/
def lpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (u : Vec 3 → ℝ) : ℝ≥0∞ :=
  eLpNorm u p (volume.restrict s)

/-- The extended `Lᵖ` seminorm of the native classical gradient. -/
def gradientLpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (u : Vec 3 → ℝ) : ℝ≥0∞ :=
  eLpNorm (classicalGradient u) p (volume.restrict s)

theorem fderiv_norm_le_three_classicalGradient
    {f : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ f x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
          have hz : z = ∑ i : Fin 3, z i • basisVec i :=
            (sum_smul_basisVec z).symm
          rw [hz, map_sum]
          simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hz : |z i| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hg : |(fderiv ℝ f x) (basisVec i)| ≤ ‖classicalGradient f x‖ := by
        simpa only [classicalGradient_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (classicalGradient f x) i
      exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

/- The fixed factor is absolute because the ambient dimension is three. -/
/-- Euclidean Sobolev coefficient inherited from Mathlib's compact-support inequality. -/
noncomputable def localSobolevConstant : ℝ≥0∞ :=
  ((3 : NNReal) : ℝ≥0∞) *
    (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
      (2 : ℝ) : ℝ≥0∞)

end
end CKN
