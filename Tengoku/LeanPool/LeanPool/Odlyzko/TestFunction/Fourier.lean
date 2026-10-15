/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Basic
public import Tengoku
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Amplitude

/-! TODO: Add doc-string. -/

@[expose] public section

section

open MeasureTheory Set

namespace NumberField.Odlyzko

/--
@isnad1 id=le.0h0v.s4.be9700571b2b from=translated src=- shape=66c352d6 vocab=f1774588
-/
theorem support_tartarWeight_subset :
    Function.support Tartar.weight ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  simp only [mem_Icc, neg_le]
  constructor <;> by_contra h
  · exact hx (tartarWeight_eq_zero_of_one_le_abs (by
      grind))
  · exact hx (tartarWeight_eq_zero_of_one_le_abs (by
      grind))

/--
@isnad1 id=hascompa.0h0v.s3.b7881981cc2a from=translated src=- shape=e3d48bcb vocab=b288b88c
-/
theorem tartarWeight_hasCompactSupport : HasCompactSupport Tartar.weight :=
  IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    (closure_minimal support_tartarWeight_subset isClosed_Icc)

/--
@isnad1 id=integrab.0h0v.s4.e945674a39e4 from=translated src=- shape=e14394ff vocab=7eb3ad70
-/
theorem tartarWeight_integrable : Integrable Tartar.weight :=
  tartarWeight_continuous.integrable_of_hasCompactSupport tartarWeight_hasCompactSupport

/--
@isnad1 id=eq.0h0v.s5.bdbabcaa607c from=translated src=- shape=59ef8cb2 vocab=27178edb
-/
theorem tartarWeight_eq_indicator :
    Tartar.weight = (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ 1 - x ^ 2) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact tartarWeight_eq_one_sub_sq_of_abs_le_one (by grind)
  · rw [Set.indicator_of_notMem hx]
    apply tartarWeight_eq_zero_of_one_le_abs
    grind

/--
@isnad1 id=eq.0h0v.s5.a1c6025bb92f from=translated src=- shape=71d3640f vocab=1bbdeee3
-/
theorem integral_tartarWeight :
    ∫ x : ℝ, Tartar.weight x = 4 / 3 := by
  rw [tartarWeight_eq_indicator, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const, integral_pow]
  norm_num

end NumberField.Odlyzko

end

section

open MeasureTheory Set

namespace NumberField.Odlyzko

/--
@isnad1 id=eq.1h1v.s7.5c941573876e from=translated src=- shape=ff8a6d74 vocab=111e2124
-/
theorem intervalIntegral_one_sub_sq_mul_cos {x : ℝ} (hx : x ≠ 0) :
    ∫ t : ℝ in (-1)..1, (1 - t ^ 2) * Real.cos (x * t) =
      4 * (Real.sin x - x * Real.cos x) / x ^ 3 := by
  let F : ℝ → ℝ := fun t ↦
    (1 - t ^ 2) * Real.sin (x * t) / x -
      2 * t * Real.cos (x * t) / x ^ 2 +
      2 * Real.sin (x * t) / x ^ 3
  have hF (t : ℝ) :
      HasDerivAt F ((1 - t ^ 2) * Real.cos (x * t)) t := by
    have hsin : HasDerivAt (fun u : ℝ ↦ Real.sin (x * u))
        (Real.cos (x * t) * x) t := by
      convert ((hasDerivAt_id t).const_mul x).sin using 1 <;> simp
    have hcos : HasDerivAt (fun u : ℝ ↦ Real.cos (x * u))
        (-Real.sin (x * t) * x) t := by
      convert ((hasDerivAt_id t).const_mul x).cos using 1 <;> simp
    dsimp [F]
    have hraw := ((((hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2)).mul hsin).div_const x
      |>.sub ((((hasDerivAt_const t 2).mul (hasDerivAt_id t)).mul hcos).div_const (x ^ 2))
      |>.add (((hasDerivAt_const t 2).mul hsin).div_const (x ^ 3)))
    convert hraw using 1
    all_goals try rfl
    · field_simp
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t)]
  · dsimp [F]
    simp only [one_pow, neg_sq, mul_one, mul_neg, Real.sin_neg, Real.cos_neg]
    grind
  · exact (by fun_prop : Continuous (fun t : ℝ ↦
      (1 - t ^ 2) * Real.cos (x * t))).intervalIntegrable _ _

/--
@isnad1 id=eq.0h1v.s6.fc69595bab70 from=translated src=- shape=88a0ad35 vocab=764d30a6
-/
theorem tartarAmplitude_eq_cosineTransform (x : ℝ) :
    Tartar.amplitude x = (3 / 4 : ℝ) * ∫ t : ℝ, Tartar.weight t * Real.cos (x * t) := by
  by_cases hx : x = 0
  · subst x
    simp [integral_tartarWeight]
  · rw [tartarWeight_eq_indicator]
    have hind :
        (fun t : ℝ ↦
          (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * Real.cos (x * t)) =
        (Set.Icc (-1 : ℝ) 1).indicator
          (fun t ↦ (1 - t ^ 2) * Real.cos (x * t)) := by
      funext t
      exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
        (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ Real.cos (x * u))).symm
    rw [hind]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral_one_sub_sq_mul_cos hx, tartarAmplitude_eq_of_ne hx]
    grind

/--
@isnad1 id=integrab.0h1v.s5.c7c8ad4dceea from=translated src=- shape=a7355a5f vocab=10487abd
-/
theorem tartarWeight_mul_cos_integrable (x : ℝ) :
    Integrable (fun t : ℝ ↦ Tartar.weight t * Real.cos (x * t)) := by
  apply tartarWeight_integrable.mul_bdd
  · exact (by fun_prop : Continuous (fun t : ℝ ↦ Real.cos (x * t))).aestronglyMeasurable
  · filter_upwards [] with t
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (x * t)

/--
@isnad1 id=le.0h1v.s6.025b79d88fbc from=translated src=- shape=be8f70e6 vocab=edc70635
-/
theorem norm_integral_tartarWeight_mul_cos_le (x : ℝ) :
    ‖∫ t : ℝ, Tartar.weight t * Real.cos (x * t)‖ ≤ 4 / 3 := by
  calc
    ‖∫ t : ℝ, Tartar.weight t * Real.cos (x * t)‖
        ≤ ∫ t : ℝ, Tartar.weight t :=
      norm_integral_le_of_norm_le tartarWeight_integrable <| .of_forall fun t ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tartarWeight_nonneg t)]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (tartarWeight_nonneg t)).trans_eq
          (mul_one _)
    _ = 4 / 3 := integral_tartarWeight

/--
@isnad1 id=le.0h1v.s4.54f8c6659c1b from=translated src=- shape=38becc55 vocab=bb059b28
-/
theorem abs_tartarAmplitude_le_one (x : ℝ) : |Tartar.amplitude x| ≤ 1 := by
  rw [tartarAmplitude_eq_cosineTransform, abs_mul]
  have h := norm_integral_tartarWeight_mul_cos_le x
  rw [Real.norm_eq_abs] at h
  norm_num
  nlinarith

/--
@isnad1 id=le.0h1v.s3.919153072c9f from=translated src=- shape=b14ee516 vocab=d1780e24
-/
theorem tartarTestFunction_le_one (x : ℝ) : Tartar.testFunction x ≤ 1 := by
  rw [Tartar.testFunction]
  have h := (sq_le_sq₀ (abs_nonneg (Tartar.amplitude x)) zero_le_one).mpr
    (abs_tartarAmplitude_le_one x)
  simp_all

end NumberField.Odlyzko

end
