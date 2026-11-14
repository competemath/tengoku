import Tengoku.Twinprime.TwinPrime.Analytic.EvenAsymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Even-modulus errors for two independently chosen cutoffs

The actual elementary even-progression error is sublinear after weighting
at most U*V+1 moduli by log(2X+2), whenever the product of the cutoffs has
an eventual exponent strictly below one half.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

def mixedEvenWeightBudget (U V X : ℕ) : ℝ :=
  (((U * V : ℕ) : ℝ) + 1) * Real.log (2 * X + 2) * evenProgressionBound X

/--
@isnad1 id=le.0h3v.s4.d73782af8f98 from=translated src=- shape=1995cd38 vocab=5d2938a0
-/
theorem mixedEvenWeightBudget_nonneg (U V X : ℕ) :
    0 ≤ mixedEvenWeightBudget U V X := by
  unfold mixedEvenWeightBudget
  apply mul_nonneg _ (evenProgressionBound_nonneg X)
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  have := Nat.cast_nonneg (α := ℝ) X
  linarith

/--
@isnad1 id=le.2h4v.s7.54ff8a713aa5 from=translated src=- shape=05cbc023 vocab=5736a3bd
-/
theorem mixedEvenWeightBudget_le_of_product_le (U V X : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hUV : ((U * V : ℕ) : ℝ) ≤ (2 * X + 2 : ℝ) ^ a) :
    mixedEvenWeightBudget U V X ≤
      4 * (2 * X + 2 : ℝ) ^ (a + 1 / 2) * (Real.log (2 * X + 2)) ^ 2 := by
  let Y : ℝ := 2 * X + 2
  have hY : 1 ≤ Y := by
    dsimp [Y]
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hOne : 1 ≤ Y ^ a := Real.one_le_rpow hY ha
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hcap : ((U * V : ℕ) : ℝ) + 1 ≤ 2 * Y ^ a := by
    change ((U * V : ℕ) : ℝ) ≤ Y ^ a at hUV
    linarith
  have hpow : Y ^ a * Real.sqrt Y = Y ^ (a + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : 0 < Y)]
  change (((U * V : ℕ) : ℝ) + 1) * Real.log Y *
    (2 * Real.sqrt Y * Real.log Y) ≤ _
  change _ ≤ 4 * Y ^ (a + 1 / 2) * (Real.log Y) ^ 2
  calc
    _ ≤ (2 * Y ^ a) * Real.log Y * (2 * Real.sqrt Y * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcap (Real.log_nonneg hY)
    _ = _ := by rw [← hpow]; ring

/-- Only the eventual product bound is needed; either cutoff may otherwise
vary arbitrarily, and zero cutoffs and the initial endpoint are permitted.
@isnad1 id=tendsto.3h3v.s7.63045c898a32 from=translated src=- shape=897e35ed vocab=22d523a5
-/
theorem tendsto_mixedEvenWeightBudget_div_of_product_le (U V : ℕ → ℕ)
    (a : ℝ) (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ => mixedEvenWeightBudget (U X) (V X) X / X)
      atTop (nhds 0) := by
  have h := (tendsto_dyadic_power_log_sq_div (a := a + 1 / 2) (by linarith)).const_mul 4
  simp only [mul_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact div_nonneg (mixedEvenWeightBudget_nonneg _ _ _) (Nat.cast_nonneg X)
  · filter_upwards [hUV] with X hX
    have hbase : (X : ℝ) ^ a ≤ (2 * X + 2 : ℝ) ^ a := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg X) _ ha
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    have hb := mixedEvenWeightBudget_le_of_product_le (U X) (V X) X a ha
      (hX.trans hbase)
    simpa only [mul_div_assoc, mul_assoc] using
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg X)

end TwinPrime.Analytic
