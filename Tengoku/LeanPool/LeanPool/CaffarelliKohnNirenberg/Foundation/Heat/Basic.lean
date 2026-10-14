/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# The three-dimensional heat kernel

This file fixes the Gaussian normalization used by the parabolic estimates.
The spatial variable is the repository's `Fin 3 → ℝ` type, and the spatial
quadratic form is written as a finite sum so that it is independent of the
ambient sup norm on the function space.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! ### Definitions and elementary identities -/

/-- Three-dimensional Gaussian heat kernel, extended by zero to nonpositive time. -/
def heatKernel (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, x i ^ 2) / (4 * t))
  else 0

/-- Causal heat kernel on parabolic points. -/
def heatKernelPlus (p : ParabolicPoint) : ℝ :=
  if 0 < p.2 then heatKernel p.1 p.2 else 0

/-- Sum of spatial Euclidean length and the square root of time used in kernel estimates. -/
def rhoTwo (x : Vec3) (t : ℝ) : ℝ :=
  vec3EuclideanNorm x + Real.sqrt t

/--
@isnad1 id=eq.0h1v.s6.a25fa18c3fc4 from=translated src=- shape=b3d7bd61 vocab=e3c500d9
-/
lemma vec3EuclideanNorm_sq (x : Vec3) :
    (vec3EuclideanNorm x) ^ 2 = ∑ i, x i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (x i))

/--
@isnad1 id=eq.1h2v.s4.9ddd61f68bbd from=translated src=- shape=a7faa7d3 vocab=4021115e
-/
lemma heatKernel_eq_zero_of_nonpos {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    heatKernel x t = 0 := by
  simp [heatKernel, not_lt.mpr ht]

/--
@isnad1 id=eq.1h2v.s7.642d10ba593f from=translated src=- shape=a85ff9ca vocab=89c38e24
-/
lemma heatKernel_eq_formula {x : Vec3} {t : ℝ} (ht : 0 < t) :
  heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t)) := by
  rw [heatKernel, ite_eq_left ht, vec3EuclideanNorm_sq]

/--
@isnad1 id=eq.1h2v.s7.bef3986fe528 from=translated src=- shape=b726c23d vocab=0476075a
-/
lemma heatKernel_eq_formula_sum {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) := by
  rw [heatKernel_eq_formula ht, vec3EuclideanNorm_sq]

/--
@isnad1 id=le.0h2v.s4.eff764bb149c from=translated src=- shape=787c1379 vocab=4021115e
-/
lemma heatKernel_nonneg (x : Vec3) (t : ℝ) : 0 ≤ heatKernel x t := by
  by_cases ht : 0 < t
  · rw [heatKernel_eq_formula ht]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.exp_pos _).le
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)]

/--
@isnad1 id=lt.1h2v.s4.7b7a0a74ed3e from=translated src=- shape=696abc3b vocab=0bf6cd85
-/
lemma heatKernel_pos {x : Vec3} {t : ℝ} (ht : 0 < t) :
    0 < heatKernel x t := by
  rw [heatKernel_eq_formula ht]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/--
@isnad1 id=eq.0h1v.s3.1cc52518f02e from=translated src=- shape=9eaa1e11 vocab=89f3f9db
-/
lemma heatKernelPlus_eq_heatKernel (p : ParabolicPoint) :
    heatKernelPlus p = heatKernel p.1 p.2 := by
  by_cases ht : 0 < p.2
  · simp [heatKernelPlus, ht]
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)]
    simp [heatKernelPlus, ht]

/--
@isnad1 id=eq.1h2v.s4.f417f8f1e2d5 from=translated src=- shape=78deb4b1 vocab=24e1067a
-/
lemma heatKernelPlus_eq_zero_of_nonpos {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    heatKernelPlus (x, t) = 0 := by
  simp [heatKernelPlus, not_lt.mpr ht]

private lemma gaussian_sum_exp_eq_prod (x : Vec3) (t : ℝ) :
    Real.exp (-(∑ i, x i ^ 2) / (4 * t)) =
      ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2) := by
  rw [show -(∑ i, x i ^ 2) / (4 * t) =
      ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) by
    calc
      -(∑ i, x i ^ 2) / (4 * t) =
          (-1 / (4 * t)) * (∑ i, x i ^ 2) := by
            field_simp
      _ = ∑ i, (-1 / (4 * t)) * (x i) ^ 2 := by rw [Finset.mul_sum]
      _ = ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) := by ring_nf]
  exact Real.exp_sum Finset.univ (fun i => -(1 / (4 * t)) * (x i) ^ 2)

private lemma gaussian_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * t))) volume := by
  rw [show volume = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) by
    exact volume_pi]
  have hprod : Integrable
      (fun x : Vec3 => ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2))
      (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) := by
    exact Integrable.fintype_prod (ι := Fin 3) (E := ℝ)
      (μ := fun _ : Fin 3 => (volume : Measure ℝ)) (fun _hi => by
      convert integrable_exp_neg_mul_sq
        (by positivity : 0 < (1 / (4 * t) : ℝ)) using 1)
  exact hprod.congr (Filter.Eventually.of_forall fun x =>
    (gaussian_sum_exp_eq_prod x t).symm)

/--
@isnad1 id=integrab.1h1v.s6.9dd71076f15b from=translated src=- shape=4aa00920 vocab=3b36b515
-/
lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernel x t) volume := by
  rw [show (fun x : Vec3 => heatKernel x t) = fun x : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) by
    funext x
    exact heatKernel_eq_formula_sum ht]
  exact (gaussian_integrable t ht).const_mul _

/--
@isnad1 id=eq.1h1v.s7.3177529398fc from=translated src=- shape=9e17b4ee vocab=1d2305a5
-/
lemma gaussian_integral (t : ℝ) (ht : 0 < t) :
    ∫ x : Vec3, Real.exp (-(∑ i, x i ^ 2) / (4 * t)) =
      (Real.sqrt (4 * Real.pi * t)) ^ (3 : ℕ) := by
  rw [show volume = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) by
    exact volume_pi]
  have hfun : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * t))) =
      (fun x : Vec3 => ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2)) := by
    funext x
    exact gaussian_sum_exp_eq_prod x t
  have hprod := integral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (fun _ : Fin 3 => fun y : ℝ => Real.exp (-(1 / (4 * t)) * y ^ 2))
  rw [hfun]
  rw [show (∫ x : Vec3, ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) =
      ∏ i : Fin 3, ∫ y : ℝ, Real.exp (-(1 / (4 * t)) * y ^ 2) by
    exact hprod]
  simp only [Finset.prod_const, Finset.card_fin]
  rw [integral_gaussian (1 / (4 * t))]
  congr 1
  field_simp [ht.ne']

/--
@isnad1 id=eq.1h1v.s6.dadff7099061 from=translated src=- shape=3557dc68 vocab=abf0ed94
-/
lemma heatKernel_integral (t : ℝ) (ht : 0 < t) :
    ∫ x : Vec3, heatKernel x t = 1 := by
  rw [show (fun x : Vec3 => heatKernel x t) = fun x : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) by
    funext x
    exact heatKernel_eq_formula_sum ht]
  rw [integral_const_mul, gaussian_integral t ht]
  have hbase : 0 < 4 * Real.pi * t := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hbase.le]
  have hexp : (1 / 2 : ℝ) * (↑(3 : ℕ) : ℝ) = (3 : ℝ) / 2 := by norm_num
  rw [hexp]
  rw [← Real.rpow_add hbase]
  simp only [show -(3 : ℝ) / 2 + (3 : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/--
@isnad1 id=le.0h1v.s3.2d79e1af780b from=translated src=- shape=b9369acb vocab=f3803edb
-/
lemma heatKernelPlus_nonneg (p : ParabolicPoint) : 0 ≤ heatKernelPlus p := by
  rw [heatKernelPlus_eq_heatKernel]
  exact heatKernel_nonneg _ _

end CKN.Foundation.Heat
