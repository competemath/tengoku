/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyEnergy
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyC1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleySplit
public import Tengoku

/-!
# Gradient energy bounds for the two-reflection extension

The chain rule and the operator-norm estimates from `SeeleyBounds` are
combined with the pullback estimates from `SeeleyEnergy`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/--
@isnad1 id=le.0h2v.s9.8c09fab4e68b from=translated src=- shape=23966c47 vocab=6346732c
-/
theorem seeley_fderiv_norm_le_three_classicalGradient
    (f : Vec 3 → ℝ) (x : Vec 3) :
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

end
end CKN
