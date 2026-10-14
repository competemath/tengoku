import Tengoku
import Tengoku.Formalbook.FormalBook.Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Tengoku.Formalbook.FormalBook.Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

attribute [local simp] intervalIntegral.intervalIntegrable_inv_sqrt_one_sub_sq

open Real Set

/--
@isnad1 id=eq.0h2v.s6.1e3fb6c389c1 from=translated src=- shape=666b47f8 vocab=316fc585
-/
@[simp]
theorem intervalIntegral.integral_inv_sqrt_one_sub_sq {a b : ℝ} :
    ∫ x : ℝ in a..b, (√(1 - x ^ 2))⁻¹ = (arcsin b - arcsin a) := by
  convert_to (∫ x : ℝ in a..-1, (√(1 - x ^ 2))⁻¹) + ∫ x : ℝ in -1..b, (√(1 - x ^ 2))⁻¹ =
      (arcsin (-1) - arcsin a) + (arcsin b - arcsin (-1)) using 1
  · simp [integral_add_adjacent_intervals]
  · ring
  suffices ∀ t, ∫ x : ℝ in -1..t, (√(1 - x ^ 2))⁻¹ = arcsin t - arcsin (-1) by
    congr 2
    · rw [integral_symm, this a, neg_sub]
    · rw [this b]
  clear a b
  intro t
  wlog ht : t ≤ 1
  · replace ht := le_of_not_ge ht
    calc
      _ = (∫ x : ℝ in -1..1, (√(1 - x ^ 2))⁻¹) + ∫ x : ℝ in 1..t, (√(1 - x ^ 2))⁻¹ := by
        simp [integral_add_adjacent_intervals]
      _ = π + ∫ x : ℝ in 1..t, 0 := by
        congr 1
        · simpa using this 1 (by norm_num)
        · refine integral_congr fun x hx => ?_
          rw [inv_eq_zero, sqrt_eq_zero']
          suffices x ≤ -1 ∨ x ≥ 1 by rcases this with this | this <;> nlinarith only [this]
          simp [uIcc] at hx
          grind only
      _ = _ := by simp [←pi_div_two_eq_arcsin.mpr ht]
  calc
    _ = ∫ x : ℝ in -1..t, deriv arcsin x := by simp [deriv_arcsin]
    _ = _ := by
      apply intervalIntegral.integral_deriv_eq_sub_uIoo
      · apply continuous_arcsin.continuousOn
      · intro x hx
        simp [uIoo] at hx
        rw [differentiableAt_arcsin]
        grind only
      · simp

/--
@isnad1 id=eq.1h3v.s6.2deb431768fa from=translated src=- shape=443c0ce3 vocab=49be4199
-/
@[simp, nolint simpNF]
theorem intervalIntegral.integral_inv_sq_add_sq {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, (c ^ 2 + x ^ 2)⁻¹ = c⁻¹ * (arctan (b / c) - arctan (a / c)) := calc
  _ = ∫ x : ℝ in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [intervalIntegral.integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp
