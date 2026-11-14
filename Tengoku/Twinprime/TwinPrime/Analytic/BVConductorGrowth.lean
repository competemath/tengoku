import Tengoku.Twinprime.TwinPrime.Analytic.VaughanMeanValue
import Tengoku.Twinprime.TwinPrime.Analytic.GrowthBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic absorption of the proved large-conductor budget

The actual centered conductor tail at `2X+2`, including the reciprocal-totient
logarithmic factor, has arbitrary logarithmic saving in the stated BV range.
The lower conductor cutoff is arbitrary within that range. No distribution
or character mean-value hypothesis is used.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- A finite numerical bound, with the power margin supplied explicitly.-/
theorem bvLargeConductorBudget_le_log_saving (A : ℝ) (hA : 0 < A)
    (X R₀ Q : ℕ) (hX : 256 ≤ X) (hR₀ : 1 ≤ R₀) (hRQ : R₀ ≤ Q)
    (hR : (Real.log X) ^ (A + 9) ≤ (R₀ : ℝ))
    (hQ : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 9))
    (hmargin : (Real.log X) ^ (A + 8) ≤ (X : ℝ) ^ (1 / 16 : ℝ)) :
    totientReciprocalConstant * (1 + Real.log Q) *
        bvLargeConductorBudget (2 * X + 2) R₀ Q ≤
      (768 * totientReciprocalConstant * bvMeanConstant) * X / (Real.log X) ^ A := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hx0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl1 : 1 ≤ Real.log (X : ℝ) := one_le_log_of_256_le X hX
  have hl0 : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hl0 _
  have hp0 : 0 < (Real.log X) ^ (A + 9) := Real.rpow_pos_of_pos hl0 _
  have hp1 : 1 ≤ (Real.log X) ^ (A + 9) :=
    Real.one_le_rpow hl1 (by linarith)
  have hr0 : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hqroot : (Q : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have hdiv : Real.sqrt (X : ℝ) / (Real.log X) ^ (A + 9) ≤ Real.sqrt X := by
      apply (div_le_iff₀ hp0).mpr
      nlinarith [mul_nonneg (Real.sqrt_nonneg (X : ℝ)) (sub_nonneg.mpr hp1)]
    apply le_trans _ hdiv
    simpa only [Real.sqrt_eq_rpow] using hQ
  have hlq : 1 + Real.log (Q : ℝ) ≤ Real.log X :=
    one_add_log_modulus_le_log X Q hX (by omega) hqroot
  have ht4 : (2 * X + 2 : ℝ) ≤ 4 * X := by linarith
  have hlt : Real.log (2 * X + 2 : ℝ) ≤ 2 * Real.log X :=
    log_two_mul_add_two_le_two_log (by omega)
  have hlt0 : 0 ≤ Real.log (2 * X + 2 : ℝ) := Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt (2 * X + 2 : ℝ) ≤ 2 * Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx0.le]
  have htPower : (2 * X + 2 : ℝ) ^ (15 / 16 : ℝ) ≤
      4 * (X : ℝ) ^ (15 / 16 : ℝ) := by
    calc
      _ ≤ (4 * X : ℝ) ^ (15 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) ht4 (by norm_num)
      _ = (4 : ℝ) ^ (15 / 16 : ℝ) * (X : ℝ) ^ (15 / 16 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hx0.le]
      _ ≤ _ := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
          (by norm_num : (15 / 16 : ℝ) ≤ 1)).trans_eq (Real.rpow_one 4)
  have hratio : (Q : ℝ) / R₀ ≤ Q := by
    apply (div_le_iff₀ hr0).mpr
    have hr1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR₀
    nlinarith
  have hlogratio : 1 + Real.log ((Q : ℝ) / R₀) ≤ Real.log X := by
    linarith [Real.log_le_log (div_pos hq0 hr0) hratio]
  have hlogratio0 : 0 ≤ 1 + Real.log ((Q : ℝ) / R₀) := by
    have hrat1 : (1 : ℝ) ≤ (Q : ℝ) / R₀ := by
      apply (le_div_iff₀ hr0).mpr
      simpa using (show (R₀ : ℝ) ≤ Q by exact_mod_cast hRQ)
    have := Real.log_nonneg hrat1
    linarith
  have hfirst : (2 * X + 2 : ℝ) / R₀ ≤ 4 * X / (Real.log X) ^ (A + 9) := by
    exact div_le_div₀ (by positivity) ht4 hp0 hR
  have hlast : 2 * Real.sqrt (2 * X + 2 : ℝ) * Q ≤
      4 * X / (Real.log X) ^ (A + 9) := by
    calc
      _ ≤ 2 * (2 * Real.sqrt X) * (Real.sqrt X / (Real.log X) ^ (A + 9)) := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using hQ
      _ = 4 * (Real.sqrt X) ^ 2 / (Real.log X) ^ (A + 9) := by ring
      _ = _ := by rw [Real.sq_sqrt hx0.le]
  have hmiddle : (2 * X + 2 : ℝ) ^ (15 / 16 : ℝ) *
      (1 + Real.log ((Q : ℝ) / R₀)) ≤
      4 * (X : ℝ) ^ (15 / 16 : ℝ) * Real.log X :=
    mul_le_mul htPower hlogratio hlogratio0 (by positivity)
  have hinner : (2 * X + 2 : ℝ) / R₀ +
      (2 * X + 2 : ℝ) ^ (15 / 16 : ℝ) * (1 + Real.log ((Q : ℝ) / R₀)) +
        2 * Real.sqrt (2 * X + 2 : ℝ) * Q ≤
      8 * X / (Real.log X) ^ (A + 9) +
        4 * (X : ℝ) ^ (15 / 16 : ℝ) * Real.log X := by
    calc
      _ ≤ 4 * X / (Real.log X) ^ (A + 9) +
          4 * (X : ℝ) ^ (15 / 16 : ℝ) * Real.log X +
          4 * X / (Real.log X) ^ (A + 9) :=
        add_le_add (add_le_add hfirst hmiddle) hlast
      _ = _ := by ring
  have hp9 : (Real.log X) ^ (A + 9) = (Real.log X) ^ A * (Real.log X) ^ (9 : ℕ) := by
    rw [Real.rpow_add hl0, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hp8 : (Real.log X) ^ (A + 8) = (Real.log X) ^ A * (Real.log X) ^ (8 : ℕ) := by
    rw [Real.rpow_add hl0, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hshort : (Real.log X) ^ (7 : ℕ) * X / (Real.log X) ^ (A + 9) ≤
      (X : ℝ) / (Real.log X) ^ A := by
    calc
      _ ≤ (Real.log X) ^ (9 : ℕ) * X / (Real.log X) ^ (A + 9) := by
        gcongr
        norm_num
      _ = _ := by rw [hp9]; field_simp
  have hmiddleSaving : (Real.log X) ^ (8 : ℕ) * (X : ℝ) ^ (15 / 16 : ℝ) ≤
      (X : ℝ) / (Real.log X) ^ A := by
    apply (le_div_iff₀ hs0).mpr
    calc
      _ = (Real.log X) ^ (A + 8) * (X : ℝ) ^ (15 / 16 : ℝ) := by rw [hp8]; ring
      _ ≤ (X : ℝ) ^ (1 / 16 : ℝ) * (X : ℝ) ^ (15 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right hmargin (by positivity)
      _ = X := by rw [← Real.rpow_add hx0]; norm_num
  have hc : 0 ≤ totientReciprocalConstant := totientReciprocalConstant_nonneg
  have hC : 0 ≤ bvMeanConstant := bvMeanConstant_pos.le
  have hbudget : bvLargeConductorBudget (2 * X + 2) R₀ Q ≤
      bvMeanConstant * (2 * Real.log X) ^ (6 : ℕ) *
        (8 * X / (Real.log X) ^ (A + 9) +
          4 * (X : ℝ) ^ (15 / 16 : ℝ) * Real.log X) := by
    unfold bvLargeConductorBudget
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    gcongr
  calc
    _ ≤ totientReciprocalConstant * Real.log X *
        (bvMeanConstant * (2 * Real.log X) ^ (6 : ℕ) *
          (8 * X / (Real.log X) ^ (A + 9) +
            4 * (X : ℝ) ^ (15 / 16 : ℝ) * Real.log X)) := by
      have hbud0 : 0 ≤ bvLargeConductorBudget (2 * X + 2) R₀ Q := by
        unfold bvLargeConductorBudget
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlq hc) hbudget hbud0 (by positivity)
    _ = (64 * totientReciprocalConstant * bvMeanConstant) *
        (8 * ((Real.log X) ^ (7 : ℕ) * X / (Real.log X) ^ (A + 9)) +
          4 * ((Real.log X) ^ (8 : ℕ) * (X : ℝ) ^ (15 / 16 : ℝ))) := by ring
    _ ≤ (64 * totientReciprocalConstant * bvMeanConstant) *
        (8 * ((X : ℝ) / (Real.log X) ^ A) + 4 * ((X : ℝ) / (Real.log X) ^ A)) := by
      gcongr
    _ = _ := by ring

/-- The threshold is uniform in both conductor cutoffs; the constant is absolute.-/
theorem eventually_bvLargeConductorBudget_le_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop, ∀ R₀ Q : ℕ,
      1 ≤ R₀ → R₀ ≤ Q →
      (Real.log X) ^ (A + 9) ≤ (R₀ : ℝ) →
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 9) →
      totientReciprocalConstant * (1 + Real.log Q) *
          bvLargeConductorBudget (2 * X + 2) R₀ Q ≤
        K * X / (Real.log X) ^ A := by
  refine ⟨768 * totientReciprocalConstant * bvMeanConstant + 1, ?_, ?_⟩
  · have := totientReciprocalConstant_nonneg
    have := bvMeanConstant_pos
    positivity
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (A + 8) (s := 1 / 16)
    (by norm_num)).comp_tendsto tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [hsmall, eventually_ge_atTop 256] with X hsmall hX R₀ Q hR₀ hRQ hR hQ
  have hl : 0 ≤ Real.log (X : ℝ) := (one_le_log_of_256_le X hX).trans' (by norm_num)
  have hmargin : (Real.log X) ^ (A + 8) ≤ (X : ℝ) ^ (1 / 16 : ℝ) := by
    dsimp only [Function.comp_def] at hsmall
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl (A + 8)),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 16 : ℝ))] using hsmall
  apply (bvLargeConductorBudget_le_log_saving A hA X R₀ Q hX hR₀ hRQ hR hQ hmargin).trans
  gcongr
  linarith

end TwinPrime.Analytic
