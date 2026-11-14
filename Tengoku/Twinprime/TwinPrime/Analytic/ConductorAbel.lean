import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Abel bounds for the large-conductor tail

The boundary convention is valid also when the two endpoints coincide.
A quadratic cumulative bound then gives a reciprocal-weight tail estimate
with a logarithmic linear term. All statements are finite and generic.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The exact reciprocal-weighted tail, retaining both cumulative boundaries.-/
theorem sum_Ioc_div_eq_cumulative (a : ℕ → ℝ) (R₀ Q : ℕ)
    (hR : 1 ≤ R₀) (hRQ : R₀ ≤ Q) :
    (∑ r ∈ Ioc R₀ Q, a r / r) =
      coefficientSum a Q / Q - coefficientSum a R₀ / R₀ +
        ∑ r ∈ Ico R₀ Q, coefficientSum a r / ((r : ℝ) * (r + 1)) := by
  have h := reciprocalCoefficientSum_sub_eq a R₀ Q hR hRQ
  have hsplit := sum_Ioc_consecutive (fun r => a r / (r : ℝ)) (Nat.zero_le R₀) hRQ
  unfold reciprocalCoefficientSum at h
  rwa [← hsplit, add_sub_cancel_left] at h

/-- The reciprocal quadratic kernel telescopes exactly.-/
theorem sum_Ico_reciprocal_product_eq (R₀ Q : ℕ) (hR : 1 ≤ R₀) (hRQ : R₀ ≤ Q) :
    (∑ r ∈ Ico R₀ Q, (1 : ℝ) / ((r : ℝ) * (r + 1))) = 1 / (R₀ : ℝ) - 1 / Q := by
  calc
    _ = ∑ r ∈ Ico R₀ Q, (1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ)) := by
      apply sum_congr rfl
      intro r hr
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hR.trans (mem_Ico.mp hr).1
      push_cast
      field_simp
      ring
    _ = _ := by
      have h := congrArg Neg.neg (sum_Ico_sub (fun r : ℕ => 1 / (r : ℝ)) hRQ)
      rw [← sum_neg_distrib] at h
      simpa only [neg_sub] using h

/-- A finite reciprocal sum is bounded by the logarithm of the endpoint ratio.-/
theorem sum_Ico_reciprocal_succ_le_log_ratio (R₀ Q : ℕ)
    (hR : 1 ≤ R₀) (hRQ : R₀ ≤ Q) :
    (∑ r ∈ Ico R₀ Q, (1 : ℝ) / ((r : ℝ) + 1)) ≤ Real.log ((Q : ℝ) / R₀) := by
  have hR0 : (0 : ℝ) < R₀ := by exact_mod_cast hR
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hR.trans hRQ
  calc
    _ ≤ ∑ r ∈ Ico R₀ Q, (Real.log ((r + 1 : ℕ) : ℝ) - Real.log r) := by
      apply sum_le_sum
      intro r hr
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hR.trans (mem_Ico.mp hr).1
      have hr1 : (0 : ℝ) < r + 1 := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hr1 hr0)
      rw [Real.log_div hr1.ne' hr0.ne'] at h
      push_cast
      have heq : (1 : ℝ) / ((r : ℝ) + 1) = 1 - (((r : ℝ) + 1) / r)⁻¹ := by
        field_simp
        ring
      rw [heq]
      exact h
    _ = Real.log Q - Real.log R₀ := sum_Ico_sub (fun r : ℕ => Real.log (r : ℝ)) hRQ
    _ = _ := (Real.log_div hQ0.ne' hR0.ne').symm

/-- A nonnegative coefficient sequence with a quadratic cumulative bound
has the reciprocal-weight tail required for the conductor decomposition.-/
theorem sum_Ioc_div_le_of_cumulative_quadratic
    (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (R₀ Q : ℕ)
    (hR : 1 ≤ R₀) (hRQ : R₀ ≤ Q) (A B D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hS : ∀ r ∈ Icc R₀ Q, coefficientSum a r ≤ A + B * r + D * (r : ℝ) ^ 2) :
    (∑ r ∈ Ioc R₀ Q, a r / r) ≤
      A / R₀ + B * (1 + Real.log ((Q : ℝ) / R₀)) + 2 * D * Q := by
  have hR0 : (0 : ℝ) < R₀ := by exact_mod_cast hR
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hR.trans hRQ
  have hS0 : 0 ≤ coefficientSum a R₀ := sum_nonneg fun r _ => ha r
  have hendpoint : coefficientSum a Q / Q ≤ A / Q + B + D * Q := by
    calc
      _ ≤ (A + B * Q + D * (Q : ℝ) ^ 2) / Q :=
        div_le_div_of_nonneg_right (hS Q (mem_Icc.mpr ⟨hRQ, le_rfl⟩)) hQ0.le
      _ = _ := by field_simp
  have hkernel : (∑ r ∈ Ico R₀ Q, coefficientSum a r / ((r : ℝ) * (r + 1))) ≤
      A * (1 / (R₀ : ℝ) - 1 / Q) + B * Real.log ((Q : ℝ) / R₀) + D * Q := by
    calc
      _ ≤ ∑ r ∈ Ico R₀ Q,
          (A * (1 / ((r : ℝ) * (r + 1))) + B * (1 / ((r : ℝ) + 1)) + D) := by
        apply sum_le_sum
        intro r hr
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hR.trans (mem_Ico.mp hr).1
        have hr1 : (0 : ℝ) < r + 1 := by positivity
        calc
          _ ≤ (A + B * r + D * (r : ℝ) ^ 2) / ((r : ℝ) * (r + 1)) :=
            div_le_div_of_nonneg_right
              (hS r (mem_Icc.mpr ⟨(mem_Ico.mp hr).1, (mem_Ico.mp hr).2.le⟩)) (by positivity)
          _ = A * (1 / ((r : ℝ) * (r + 1))) + B * (1 / ((r : ℝ) + 1)) +
              D * r / ((r : ℝ) + 1) := by field_simp
          _ ≤ _ := by
            apply add_le_add le_rfl
            apply (div_le_iff₀ hr1).mpr
            nlinarith
      _ = A * (∑ r ∈ Ico R₀ Q, (1 : ℝ) / ((r : ℝ) * (r + 1))) +
          B * (∑ r ∈ Ico R₀ Q, (1 : ℝ) / ((r : ℝ) + 1)) + ((Q - R₀ : ℕ) : ℝ) * D := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ A * (1 / (R₀ : ℝ) - 1 / Q) + B * Real.log ((Q : ℝ) / R₀) + (Q : ℝ) * D := by
        apply add_le_add
        · exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_Ico_reciprocal_product_eq R₀ Q hR hRQ).le hA)
            (mul_le_mul_of_nonneg_left (sum_Ico_reciprocal_succ_le_log_ratio R₀ Q hR hRQ) hB)
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le Q R₀) hD
      _ = _ := by ring
  rw [sum_Ioc_div_eq_cumulative a R₀ Q hR hRQ]
  have hdrop : 0 ≤ coefficientSum a R₀ / R₀ := div_nonneg hS0 hR0.le
  calc
    _ ≤ (A / Q + B + D * Q) +
        (A * (1 / (R₀ : ℝ) - 1 / Q) + B * Real.log ((Q : ℝ) / R₀) + D * Q) := by
      linarith
    _ = _ := by ring

end TwinPrime.Analytic
