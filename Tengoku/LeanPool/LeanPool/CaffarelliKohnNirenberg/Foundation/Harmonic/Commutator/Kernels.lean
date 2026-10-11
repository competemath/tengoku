/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Commutator.KernelsBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku

/-!
# Kernels

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

theorem newtonianKernel_eq_scaled (m j l : Fin 3) (x : CKN.Vec 3) :
    newtonianKernel m j l x = -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x := by
  rfl

theorem newtonianKernel_size_bound {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l : Fin 3) :
    |newtonianKernel m j l x| ≤
      (24 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-4 : ℝ) := by
  let r := CKN.vecEuclideanNorm x
  have hr : 0 < r := by
    dsimp [r]
    apply lt_of_le_of_ne (CKN.vecEuclideanNorm_nonneg x)
    intro h
    apply hx
    exact CKN.vecEuclideanNorm_eq_zero_iff.mp h.symm
  have hcoord (i : Fin 3) : |x i| ≤ r :=
    abs_apply_le_vecEuclideanNorm x i
  have hr4 : r ^ (-4 : ℝ) = (r ^ 4)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hr5 : r ^ (-5 : ℝ) = (r ^ 5)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hr7 : r ^ (-7 : ℝ) = (r ^ 7)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hterm₁ :
      |15 * x m * x j * x l * (r ^ 7)⁻¹| ≤ 15 * r ^ (-4 : ℝ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15),
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
    calc
      15 * |x m| * |x j| * |x l| * (r ^ 7)⁻¹ ≤
          15 * r * r * r * (r ^ 7)⁻¹ := by
        gcongr
        · exact hcoord m
        · exact hcoord j
        · exact hcoord l
      _ = 15 * r ^ (-4 : ℝ) := by
        rw [hr4]
        field_simp [hr.ne']
  have hterm₂ (a b : Fin 3) :
      |3 * x a * (r ^ 5)⁻¹| ≤ 3 * r ^ (-4 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg
      (inv_nonneg.mpr (pow_nonneg hr.le _))]
    calc
      3 * |x a| * (r ^ 5)⁻¹ ≤ 3 * r * (r ^ 5)⁻¹ := by
        gcongr
        exact hcoord a
      _ = 3 * r ^ (-4 : ℝ) := by
        rw [hr4]
        field_simp [hr.ne']
  have hdelta (p : Prop) [Decidable p] (a : ℝ) :
      |(if p then (1 : ℝ) else 0) * a| ≤ |a| := by
    by_cases hp : p <;> simp [hp]
  rw [newtonianKernel_eq_scaled]
  unfold inverseThirdFormula
  rw [abs_mul]
  have hscale : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hinner :
      |-15 * x m * x j * x l * (r ^ 7)⁻¹ +
          3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| ≤
        24 * r ^ (-4 : ℝ) := by
    have hsum :
        |(if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m| ≤
        |x j| + |x l| + |x m| := by
      calc
        _ ≤ |(if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l| +
            |(if l = j then 1 else 0) * x m| := abs_add_le _ _
        _ ≤ (|(if m = l then 1 else 0) * x j| +
            |(if m = j then 1 else 0) * x l|) +
            |(if l = j then 1 else 0) * x m| := by
          exact add_le_add_left
            (abs_add_le ((if m = l then 1 else 0) * x j)
              ((if m = j then 1 else 0) * x l)) _
        _ ≤ |x j| + |x l| + |x m| := by
          exact add_le_add (add_le_add (hdelta (m = l) (x j))
            (hdelta (m = j) (x l))) (hdelta (l = j) (x m))
    have hsumKernel :
        |3 * ((if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| ≤
        9 * r ^ (-4 : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      calc
        3 * |(if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m| * (r ^ 5)⁻¹ ≤
            3 * (|x j| + |x l| + |x m|) * (r ^ 5)⁻¹ := by
          gcongr
        _ ≤ 3 * (r + r + r) * (r ^ 5)⁻¹ := by
          gcongr <;> exact hcoord _
        _ = 9 * r ^ (-4 : ℝ) := by
          rw [hr4]
          field_simp [hr.ne']
          ring_nf
    calc
      _ ≤ |15 * x m * x j * x l * (r ^ 7)⁻¹| +
          |3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| := by
        rw [show -15 * x m * x j * x l * (r ^ 7)⁻¹ =
          -(15 * x m * x j * x l * (r ^ 7)⁻¹) by ring_nf]
        simpa only [abs_neg] using (abs_add_le
          (-(15 * x m * x j * x l * (r ^ 7)⁻¹))
          (3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹))
      _ ≤ 24 * r ^ (-4 : ℝ) := by
        exact (add_le_add hterm₁ hsumKernel).trans_eq (by ring_nf)
  rw [show CKN.vecEuclideanNorm x = r by rfl]
  rw [abs_neg, abs_of_nonneg hscale]
  apply (mul_le_mul_of_nonneg_left hinner hscale).trans_eq
  field_simp [ne_of_gt Real.pi_pos]

end
end CKN.Foundation.Harmonic.Commutator
