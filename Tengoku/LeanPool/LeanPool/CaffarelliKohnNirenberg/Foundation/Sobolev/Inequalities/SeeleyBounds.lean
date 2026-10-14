/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Seeley
public import Tengoku

/-!
# Quantitative bounds for the two-reflection extension

This file records the derivative and Jacobian estimates on the closed annulus.
The constants are deliberately coarse absolute constants; their role is to
make the change-of-variables estimates explicit.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem seeleyBounds_annulus_mem_of_closed {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) : x ∈ seeleyAnnulus := by
  exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩

private theorem seeley_closed_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ 2 :=
  hx

private theorem seeley_closed_sq_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ vecNormSq x ∧ vecNormSq x ≤ 4 := by
  have ht := seeley_closed_bounds hx
  have hsq := vecEuclideanNorm_sq x
  constructor
  · nlinarith only [ht.1, sq_nonneg (vecEuclideanNorm x - 1), hsq]
  · nlinarith only [ht.2, vecEuclideanNorm_nonneg x,
      sq_nonneg (vecEuclideanNorm x - 2), hsq]

private theorem seeley_closed_den_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ∧
      (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≤ 6 := by
  have ht := seeley_closed_bounds hx
  constructor <;> nlinarith only [ht.1, ht.2, vecEuclideanNorm_nonneg x,
    sq_nonneg (vecEuclideanNorm x - 1), sq_nonneg (vecEuclideanNorm x - 2)]

private theorem seeleyBounds_norm_le {x : Vec 3} :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem seeleyBounds_dot_abs_le {x z : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |∑ i : Fin 3, x i * z i| ≤ 6 * ‖z‖ := by
  have hxi (i : Fin 3) : |x i| ≤ 2 := by
    exact (abs_apply_le_vecEuclideanNorm x i).trans hx.2
  have hzi (i : Fin 3) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  calc
    |∑ i : Fin 3, x i * z i| ≤ ∑ i : Fin 3, |x i * z i| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => x i * z i) Finset.univ)
    _ ≤ ∑ i : Fin 3, 2 * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hxi i) (hzi i) (abs_nonneg _) (by norm_num)
    _ = 6 * ‖z‖ := by
      simp only [Fin.sum_univ_three]
      ring_nf

private theorem seeleyBounds_q_inv_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |(vecNormSq x)⁻¹| ≤ 1 := by
  have hq := seeley_closed_sq_bounds hx
  have hqpos : 0 < vecNormSq x := by linarith only [hq.1]
  rw [abs_of_pos (inv_pos.mpr hqpos)]
  exact (inv_le_one₀ hqpos).2 hq.1

private theorem seeleyBounds_q_inv_sq_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |(vecNormSq x)⁻¹ ^ 2| ≤ 1 := by
  have hi := seeleyBounds_q_inv_le hx
  rw [abs_pow]
  simpa only [one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hi

private theorem seeleyBounds_den_inv_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹| ≤ 1 := by
  have hd := seeley_closed_den_bounds hx
  have hdpos : 0 < (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x := by
    linarith only [hd.1]
  rw [abs_of_pos (inv_pos.mpr hdpos)]
  exact (inv_le_one₀ hdpos).2 hd.1

private theorem seeleyBounds_den_inv_sq_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2| ≤ 1 := by
  have hi := seeleyBounds_den_inv_le hx
  rw [abs_pow]
  simpa only [one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hi

/--
@isnad1 id=le.1h1v.s9.1030eb28e2ff from=translated src=- shape=112aa297 vocab=305b2738
-/
theorem seeleyReflectionOne_fderiv_norm_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ seeleyReflectionOne x‖ ≤ 25 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have hdot := seeleyBounds_dot_abs_le hx (z := z)
  have hcoef :
      |(vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)| ≤ 12 * ‖z‖ := by
    calc
      _ = |(vecNormSq x)⁻¹ ^ 2| * |2 * ∑ i : Fin 3, x i * z i| := abs_mul _ _
      _ ≤ 1 * (2 * (6 * ‖z‖)) := by
        gcongr
        · exact seeleyBounds_q_inv_sq_le hx
        · rw [abs_mul]
          exact mul_le_mul (by norm_num) hdot (by norm_num) (by positivity)
      _ = 12 * ‖z‖ := by ring_nf
  have hxnorm : ‖x‖ ≤ 2 :=
    (seeleyBounds_norm_le (x := x)).trans hx.2
  rw [seeleyReflectionOne_fderiv_apply (seeleyBounds_annulus_mem_of_closed hx) z]
  calc
    ‖(vecNormSq x)⁻¹ • z -
        ((vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)) • x‖ ≤
        ‖(vecNormSq x)⁻¹ • z‖ +
          ‖((vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)) • x‖ :=
      norm_sub_le _ _
    _ = |(vecNormSq x)⁻¹| * ‖z‖ +
        |(vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)| * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖z‖ + (12 * ‖z‖) * 2 := by
      exact add_le_add
        (mul_le_mul (seeleyBounds_q_inv_le hx) (le_refl (‖z‖))
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoef hxnorm (norm_nonneg _) (by positivity))
    _ ≤ 25 * ‖z‖ := by
      calc
        _ = 25 * ‖z‖ := by ring_nf
        _ ≤ _ := le_rfl

/--
@isnad1 id=le.1h1v.s9.fcceb0ff024b from=translated src=- shape=112aa297 vocab=c78bdb4f
-/
theorem seeleyReflectionTwo_fderiv_norm_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ seeleyReflectionTwo x‖ ≤ 169 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have hdot := seeleyBounds_dot_abs_le hx (z := z)
  have ht := seeley_closed_bounds hx
  have hfactor : |4 * vecEuclideanNorm x - 1| ≤ 7 := by
    rw [abs_of_nonneg]
    · linarith only [ht.2]
    · linarith only [ht.1]
  have hnormcoef :
      |(4 * vecEuclideanNorm x - 1) *
          ((2 * vecEuclideanNorm x)⁻¹ *
            (2 * ∑ i : Fin 3, x i * z i))| ≤ 84 * ‖z‖ := by
    have htpos : 0 < 2 * vecEuclideanNorm x := by
      linarith only [ht.1]
    have hinv : |(2 * vecEuclideanNorm x)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr htpos)]
      exact (inv_le_one₀ htpos).2 (by linarith only [ht.1])
    have htwo : |2 * ∑ i : Fin 3, x i * z i| ≤ 2 * (6 * ‖z‖) := by
      rw [abs_mul]
      exact mul_le_mul (by norm_num) hdot (by norm_num) (by positivity)
    have hinner : |(2 * vecEuclideanNorm x)⁻¹| *
        |2 * ∑ i : Fin 3, x i * z i| ≤ 1 * (2 * (6 * ‖z‖)) :=
      mul_le_mul hinv htwo (abs_nonneg _) (by positivity)
    calc
      _ = |4 * vecEuclideanNorm x - 1| *
          (|(2 * vecEuclideanNorm x)⁻¹| *
            |2 * ∑ i : Fin 3, x i * z i|) := by rw [abs_mul, abs_mul]
      _ ≤ 7 * (1 * (2 * (6 * ‖z‖))) := by
        exact mul_le_mul hfactor hinner (by positivity) (by norm_num)
      _ = 84 * ‖z‖ := by ring_nf
  have hcoef :
      |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))| ≤ 84 * ‖z‖ := by
    calc
      _ = |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2| *
          |(4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i))| := abs_mul _ _
      _ ≤ 1 * (84 * ‖z‖) := by
        exact mul_le_mul (seeleyBounds_den_inv_sq_le hx) hnormcoef
          (by positivity) (by positivity)
      _ = 84 * ‖z‖ := by ring_nf
  have hxnorm : ‖x‖ ≤ 2 :=
    (seeleyBounds_norm_le (x := x)).trans hx.2
  rw [seeleyReflectionTwo_fderiv_apply (seeleyBounds_annulus_mem_of_closed hx) z]
  calc
    ‖((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • z -
        (((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))) • x‖ ≤
        ‖((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • z‖ +
          ‖(((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
            ((4 * vecEuclideanNorm x - 1) *
              ((2 * vecEuclideanNorm x)⁻¹ *
                (2 * ∑ i : Fin 3, x i * z i)))) • x‖ :=
      norm_sub_le _ _
    _ = |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹| * ‖z‖ +
        |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))| * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖z‖ + (84 * ‖z‖) * 2 := by
      exact add_le_add
        (mul_le_mul (seeleyBounds_den_inv_le hx) (le_refl (‖z‖))
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoef hxnorm (by positivity) (by norm_num))
    _ ≤ 169 * ‖z‖ := by
      calc
        _ = 169 * ‖z‖ := by ring_nf
        _ ≤ _ := le_rfl

end
end CKN
