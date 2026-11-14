import Tengoku.Twinprime.TwinPrime.Analytic.ZeroFreeRectangle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strip widths for polylogarithmic conductors and heights

For `1 ≤ L`, `q ≤ L^B`, and height `L^K + 2`, the logarithmic width
and the power-gap width both dominate fixed positive multiples of
`L^(-1/2)` when the power-gap exponent is `1/(2B)`. The constant below
retains the cap `1/16` and both successive halvings of the strip width.
No character, zero-free, or prime-distribution premise is used here.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

def siegelWalfiszStripDenominator (B K : ℝ) : ℝ :=
  4000 * zeroFreeLogConstant * (1 + Real.log 7 + 2 * (B + K))

def siegelWalfiszStripWidthConstant (B K d : ℝ) : ℝ :=
  min (1 / 16) (min (siegelWalfiszStripDenominator B K)⁻¹ d) / 4

theorem siegelWalfiszStripDenominator_pos (B K : ℝ) (hB : 0 < B) (hK : 0 < K) :
    0 < siegelWalfiszStripDenominator B K := by
  have hC := zeroFreeLogConstant_pos
  have h7 : 0 ≤ Real.log (7 : ℝ) := Real.log_nonneg (by norm_num)
  unfold siegelWalfiszStripDenominator
  positivity

theorem siegelWalfiszStripWidthConstant_pos (B K d : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) :
    0 < siegelWalfiszStripWidthConstant B K d := by
  have hD := siegelWalfiszStripDenominator_pos B K hB hK
  unfold siegelWalfiszStripWidthConstant
  positivity

/-- The logarithmic denominator is at most a fixed multiple of `L^(1/2)`.
The added height margin two is included before taking the logarithm.-/
theorem primitiveLogZeroFreeWidth_polylog_lower_bound (B K L : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hL : 1 ≤ L)
    (q : ℕ) (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ L ^ B) :
    (siegelWalfiszStripDenominator B K)⁻¹ * L ^ (-(1 / 2 : ℝ)) ≤
      primitiveLogZeroFreeWidth q (L ^ K + 2) := by
  have hL0 : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hD := siegelWalfiszStripDenominator_pos B K hB hK
  have hC := zeroFreeLogConstant_pos
  have h7 : 0 ≤ Real.log (7 : ℝ) := Real.log_nonneg (by norm_num)
  have hhalf : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hLK : 1 ≤ L ^ K := Real.one_le_rpow hL hK.le
  have hlogq : Real.log q ≤ B * Real.log L := by
    calc
      _ ≤ Real.log (L ^ B) := Real.log_le_log hq0 hqL
      _ = _ := Real.log_rpow hL0 B
  have hheight : Real.log (|L ^ K + 2| + 4) ≤ Real.log 7 + K * Real.log L := by
    rw [abs_of_nonneg (by positivity : 0 ≤ L ^ K + 2)]
    calc
      _ ≤ Real.log (7 * L ^ K) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hL0 K).ne', Real.log_rpow hL0]
  have hlogL : Real.log L ≤ 2 * L ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hbudget : 1 + Real.log q + Real.log (|L ^ K + 2| + 4) ≤
      (1 + Real.log 7 + 2 * (B + K)) * L ^ (1 / 2 : ℝ) := by
    have hsmall := mul_le_mul_of_nonneg_left hlogL (by positivity : 0 ≤ B + K)
    have hconstant := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 1 + Real.log 7)
    nlinarith
  have hden : 4000 * zeroFreeLogConstant *
      (1 + Real.log q + Real.log (|L ^ K + 2| + 4)) ≤
        siegelWalfiszStripDenominator B K * L ^ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hbudget
      (by positivity : 0 ≤ 4000 * zeroFreeLogConstant)
    simpa only [siegelWalfiszStripDenominator, mul_assoc] using h
  have hden0 : 0 < 4000 * zeroFreeLogConstant *
      (1 + Real.log q + Real.log (|L ^ K + 2| + 4)) := by
    have hlogq0 := Real.log_natCast_nonneg q
    have hheight0 : 0 ≤ Real.log (|L ^ K + 2| + 4) :=
      Real.log_nonneg (by have := abs_nonneg (L ^ K + 2); linarith)
    positivity
  calc
    _ = 1 / (siegelWalfiszStripDenominator B K * L ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hL0.le]
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ _ := one_div_le_one_div_of_le hden0 hden

/-- The choice `ε=1/(2B)` cancels the conductor exponent exactly.-/
theorem polylog_conductor_power_gap_lower_bound (B L : ℝ)
    (hB : 0 < B) (hL : 1 ≤ L) (q : ℕ) (hq : 1 ≤ q)
    (hqL : (q : ℝ) ≤ L ^ B) :
    L ^ (-(1 / 2 : ℝ)) ≤ (q : ℝ) ^ (-(1 / (2 * B))) := by
  have hL0 : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h := Real.rpow_le_rpow_of_nonpos hq0 hqL
    (show -(1 / (2 * B)) ≤ 0 from neg_nonpos.mpr (by positivity))
  rw [← Real.rpow_mul hL0.le] at h
  have he : B * -(1 / (2 * B)) = -(1 / 2 : ℝ) := by
    field_simp
  rwa [he] at h

/-- A pointwise estimate whenever the logarithmic variable is at least one.-/
theorem siegelWalfiszStripWidthConstant_mul_rpow_le
    (B K d L : ℝ) (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) (hL : 1 ≤ L)
    (q : ℕ) (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ L ^ B) :
    siegelWalfiszStripWidthConstant B K d * L ^ (-(1 / 2 : ℝ)) ≤
      primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q (L ^ K + 2) / 2 := by
  let m : ℝ := min (1 / 16) (min (siegelWalfiszStripDenominator B K)⁻¹ d)
  have hD := siegelWalfiszStripDenominator_pos B K hB hK
  have hm : 0 < m := by dsimp [m]; positivity
  have hpow : 0 ≤ L ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hpow1 : L ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hcap : m * L ^ (-(1 / 2 : ℝ)) ≤ 1 / 16 :=
    (mul_le_of_le_one_right hm.le hpow1).trans (min_le_left _ _)
  have hlog : m * L ^ (-(1 / 2 : ℝ)) ≤ primitiveLogZeroFreeWidth q (L ^ K + 2) :=
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hpow).trans
      (primitiveLogZeroFreeWidth_polylog_lower_bound B K L hB hK hL q hq hqL)
  have hgap : m * L ^ (-(1 / 2 : ℝ)) ≤ d * (q : ℝ) ^ (-(1 / (2 * B))) :=
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hpow).trans
      (mul_le_mul_of_nonneg_left (polylog_conductor_power_gap_lower_bound B L hB hL q hq hqL) hd.le)
  have hmin := le_min hcap (le_min hlog hgap)
  change (m / 4) * L ^ (-(1 / 2 : ℝ)) ≤ _
  unfold primitiveZeroFreeRectangleWidth
  nlinarith

/-- Uniformity over the full polylogarithmic conductor family, with no
additional asymptotic or prime-distribution hypothesis.-/
theorem exists_siegelWalfisz_stripWidth_lower_bound (B K d : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ x : ℝ in atTop, ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
        k * (Real.log x) ^ (-(1 / 2 : ℝ)) ≤
          primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q ((Real.log x) ^ K + 2) / 2 := by
  refine ⟨siegelWalfiszStripWidthConstant B K d,
    siegelWalfiszStripWidthConstant_pos B K d hB hK hd, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
  intro q hq hqL
  exact siegelWalfiszStripWidthConstant_mul_rpow_le B K d (Real.log x) hB hK hd hx q hq hqL

end TwinPrime.Analytic
