/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.HigherBounds
public import Tengoku

/-!
# Subordination

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! The third spatial derivative is integrated in the heat-time variable.  This
is the explicit kernel corresponding to a degree-one pressure multiplier. -/

/-- Subordinated third-derivative heat kernel, integrated over times above the current time. -/
def subordinatedKernel (j l m : Fin 3) (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    -∫ s in Ioi t, heatKernelSpaceThirdDerivative x s m j l
  else 0

/-- Spatial derivative of the subordinated kernel via the fourth heat-kernel derivative. -/
def subordinatedKernelSpatialDerivative (j l m i : Fin 3) (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    -∫ s in Ioi t, heatKernelSpaceFourthDerivative x s m j l i
  else 0

private lemma third_derivative_integrableOn_Ioi {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i j k : Fin 3) :
    IntegrableOn (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k) (Ioi t) volume := by
  let C : ℝ := 1000000000000
  have hdom : IntegrableOn (fun s : ℝ => C * s ^ (-(3 : ℝ))) (Ioi t) volume := by
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul C
  have hheat : Measurable (fun s : ℝ => heatKernel x s) := by
    unfold heatKernel
    apply Measurable.ite measurableSet_Ioi
    · measurability
    · measurability
  have hcoef : Measurable (fun s : ℝ =>
      (-(x i) * (x j) * (x k) / (8 * s ^ 3) +
        ((if i = j then x k else 0) + (if i = k then x j else 0) +
          (if j = k then x i else 0)) / (4 * s ^ 2))) := by
    measurability
  have hthird : Measurable
      (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k) := by
    unfold heatKernelSpaceThirdDerivative
    apply Measurable.ite measurableSet_Ioi
    · exact hcoef.mul hheat
    · measurability
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k)
      (volume.restrict (Ioi t)) := hthird.aestronglyMeasurable.restrict
  refine hdom.mono' hmeas ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
    have hρ : Real.sqrt s ≤ rhoTwo x s := by
      unfold rhoTwo
      exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg x)
    have hbound := heatKernelSpaceThirdDerivative_abs_le_rho_inv_six
      (x := x) (t := s) hs' i j k
    have hden : 0 < rhoTwo x s := by
      unfold rhoTwo
      exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
        (Real.sqrt_pos.2 hs')
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hpow : (Real.sqrt s) ^ (6 : ℕ) = s ^ (3 : ℕ) := by
      rw [show (Real.sqrt s) ^ (6 : ℕ) = ((Real.sqrt s) ^ 2) ^ 3 by ring,
        Real.sq_sqrt hs'.le]
    have hcomp : C / rhoTwo x s ^ 6 ≤ C / (Real.sqrt s) ^ 6 := by
      gcongr
    have hrpow : s ^ (-(3 : ℝ)) = (s ^ (3 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hs'.le]
      exact congrArg Inv.inv (Real.rpow_natCast s 3)
    rw [Real.norm_eq_abs]
    calc
      |heatKernelSpaceThirdDerivative x s i j k| ≤ C / rhoTwo x s ^ 6 := by
        simpa [C] using hbound
      _ ≤ C / (Real.sqrt s) ^ 6 := hcomp
      _ = C * s ^ (-(3 : ℝ)) := by
        rw [hpow, hrpow]
        ring)

lemma subordinatedKernel_causal {j l m : Fin 3} {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    subordinatedKernel j l m x t = 0 := by
  simp [subordinatedKernel, not_lt.mpr ht]

lemma subordinatedKernel_integrable {j l m : Fin 3} {x : Vec3} {t : ℝ}
    (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => heatKernelSpaceThirdDerivative x s m j l) (Ioi t) volume := by
  exact third_derivative_integrableOn_Ioi ht m j l

lemma subordinatedKernel_timeDerivative_abs_le_rho_inv_six
    {j l m : Fin 3} {x : Vec3} {t : ℝ} (ht : 0 < t) :
    |heatKernelSpaceThirdDerivative x t m j l| ≤
      1000000000000 / rhoTwo x t ^ 6 :=
  heatKernelSpaceThirdDerivative_abs_le_rho_inv_six ht m j l

lemma subordinatedKernelSpatialDerivative_causal
    {j l m i : Fin 3} {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    subordinatedKernelSpatialDerivative j l m i x t = 0 := by
  simp [subordinatedKernelSpatialDerivative, not_lt.mpr ht]

end CKN.Foundation.Heat
