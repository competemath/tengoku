/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Convolution
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.SpaceSecondDeriv

/-!
# The Gaussian subordination identity for the Newtonian kernel

The time integral of the three-dimensional heat kernel is the Newtonian
kernel away from its singularity.  This identity is the scalar analytic
input for the heat-kernel route to the pressure decomposition.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/--
@isnad1 id=eq.1h1v.s6.243db9651b51 from=translated src=- shape=6129e06f vocab=73b769a2
-/
lemma heatKernel_integral_Ioi {x : Vec3} (hx : x ≠ 0) :
    ∫ t : ℝ in Ioi 0, heatKernel x t =
      1 / (4 * Real.pi * vec3EuclideanNorm x) := by
  have hr : 0 < vec3EuclideanNorm x := by
    rw [vec3EuclideanNorm_eq_l2]
    apply norm_pos_iff.mpr
    intro hzero
    apply hx
    exact (WithLp.toLp_injective 2) hzero
  let b : ℝ := (vec3EuclideanNorm x) ^ 2 / 4
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hheat : (fun t : ℝ => heatKernel x t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
        (t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    rw [heatKernel_eq_formula htpos]
    dsimp [b]
    rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring_nf,
      Real.mul_rpow (by positivity) htpos.le]
    have hexp : -vec3EuclideanNorm x ^ 2 / (4 * t) =
        -(vec3EuclideanNorm x) ^ 2 / 4 * t⁻¹ := by
      field_simp
    rw [hexp]
    ring_nf
  rw [integral_congr_ae hheat, integral_const_mul]
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y))
    (p := -(1 : ℝ)) (by norm_num)
  have hsub' :
      (∫ t : ℝ in Ioi 0, t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹)) =
        ∫ y : ℝ in Ioi 0, y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y) := by
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htpos : 0 < t := ht
    rw [smul_eq_mul]
    simp only [abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul htpos.le]
    have hpow : t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) =
        t ^ (-(3 : ℝ) / 2) := by
      calc
        t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) =
            t ^ ((-(1 : ℝ) - 1) + (-(1 : ℝ) * (-(1 : ℝ) / 2))) :=
          (Real.rpow_add htpos _ _).symm
        _ = t ^ (-(3 : ℝ) / 2) := by
          congr 1
          ring_nf
    calc
      t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹) =
          (t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2))) *
            Real.exp (-b * t⁻¹) := by rw [hpow]
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) * Real.exp (-b * t⁻¹)) := by
        ring_nf
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) * Real.exp (-b * t ^ (-(1 : ℝ)))) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_one]
  rw [hsub']
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := -(1 : ℝ) / 2)
    (b := b) (by norm_num) (by norm_num) hb
  have hgamma' :
      (∫ y : ℝ in Ioi 0, y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y)) =
        b ^ (-( -(1 : ℝ) / 2 + 1) / 1) * (1 / 1) * Real.Gamma
          ((-(1 : ℝ) / 2 + 1) / 1) := by
    simpa only [Real.rpow_one] using hgamma
  rw [hgamma']
  norm_num only [one_div, div_one, neg_div, neg_neg]
  rw [Real.Gamma_one_half_eq]
  dsimp [b]
  have hrpow : (vec3EuclideanNorm x ^ 2 / 4) ^ (-(1 : ℝ) / 2) =
      2 / vec3EuclideanNorm x := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have hexp : (↑(2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -1 := by norm_num
    rw [hexp, Real.rpow_neg hr.le, Real.rpow_one]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring_nf,
      Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num)]
    field_simp
  have hrpow' : (vec3EuclideanNorm x ^ 2 / 4) ^ (-(1 / 2 : ℝ)) =
      2 / vec3EuclideanNorm x := by
    convert hrpow using 1
    ring_nf
  rw [hrpow']
  have hbase : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (8 * Real.pi * Real.sqrt Real.pi)⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -((3 : ℝ) / 2) by ring_nf,
      Real.rpow_neg (by positivity)]
    have hpow : (4 * Real.pi) ^ ((3 : ℝ) / 2) =
        8 * Real.pi * Real.sqrt Real.pi := by
      rw [show (3 : ℝ) / 2 = 1 + (1 / 2 : ℝ) by ring_nf,
        Real.rpow_add (by positivity), Real.rpow_one, Real.sqrt_eq_rpow,
        Real.mul_rpow (by norm_num) (by positivity)]
      have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by norm_num)]
      rw [hfour]
      ring_nf
    rw [hpow]
  rw [hbase]
  field_simp
  ring_nf

end CKN.Foundation.Heat
