import Tengoku.Rankamplificationtotient.RankAmplification.NumberedStatementWrappers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Proposition 9.7 (`prop:transfer-diagonal`) for an arbitrary shift The paper's Proposition 9.7 fixes `2 ≤ y ≤ x` and an **arbitrary** `h ≤ y`, sets `E_h(x;y) = B_h(x;y) - D^φ_{h,>y}(x)`, records the cardinality identity `(9.7)` `0 ≤ B_h(x;y) - D^φ_{h,>y}(x) = E_h(x;y)`, and then displays `(9.8)` ``` E_h(x;y) ≪ x/y + x^{1/2} + x log x / y + x (log y)^2 / y + ∑_{y < p ≤ (2xy)^{1/2}} Ψ_τ(2xy/p², p) ``` with an absolute implied constant. -/

namespace RankAmplification

noncomputable section

/-! ## The `h`-free rescaling of the finite terms onto the paper's display -/

/-- **The rescaling step of `(9.8)`, free of the shift.** The exact finite majorant produced by the skeleton calculation, ``` 2x/y + 2⌊√(2x)⌋ + ⌊x/y⌋(1 + log⌊x/y⌋) + paperTheorem16LogSqConstant · x (log y)² / y + smoothMultiplierB4Sum x y, ``` is at most `paperTheorem16LogSqConstant` times the paper's displayed sum `x/y + x^{1/2} + x log x / y + x (log y)² / y + ∑_{y<p≤(2xy)^{1/2}} Ψ_τ(2xy/p², p)`.
@isnad1 id=le.2h2v.s7.b3e3f1e9285f from=translated src=- shape=b602b389 vocab=0b85046d
-/
theorem finiteTransferTerms_le_paperTransferDisplay {x y : ℕ} (hy : 2 ≤ y) (hxy : y ≤ x) :
    2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * ((2 * x).sqrt : ℝ) +
        (x / y : ℕ) * (1 + Real.log (x / y : ℕ)) +
        (paperTheorem16LogSqConstant * (x : ℝ) * Real.log y ^ 2 * (y : ℝ)⁻¹ +
          smoothMultiplierB4Sum x y) ≤
      paperTheorem16LogSqConstant * paperTransferDisplay x y := by
  have hC5 : (5 : ℝ) ≤ paperTheorem16LogSqConstant := five_le_paperTheorem16LogSqConstant
  have hx2 : 2 ≤ x := le_trans hy hxy
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hquot0 : (0 : ℝ) ≤ (x : ℝ) / (y : ℝ) := div_nonneg hx0 hy0.le
  -- First term: `2x/y ≤ C · x/y`.
  have hT1 : 2 * (x : ℝ) * (y : ℝ)⁻¹ ≤ paperTheorem16LogSqConstant * ((x : ℝ) / (y : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (x : ℝ) * (y : ℝ)⁻¹ := mul_nonneg hx0 (inv_nonneg.mpr hy0.le)
    have hstep := mul_le_mul_of_nonneg_right
      (show (2 : ℝ) ≤ paperTheorem16LogSqConstant by linarith) hnn
    rw [div_eq_mul_inv]
    linarith
  -- Second term: `2⌊√(2x)⌋ ≤ 4√x ≤ C·x^{1/2}`.
  have hr0 : (0 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hT2 : 2 * (((2 * x).sqrt : ℕ) : ℝ) ≤
      paperTheorem16LogSqConstant * Real.sqrt (x : ℝ) := by
    have hs0 : (0 : ℝ) ≤ (((2 * x).sqrt : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (((2 * x).sqrt : ℕ) : ℝ) ^ 2 ≤ ((2 * x : ℕ) : ℝ) := by
      exact_mod_cast Nat.sqrt_le' (2 * x)
    have hcast : ((2 * x : ℕ) : ℝ) = 2 * (x : ℝ) := by push_cast; ring
    have hsq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
    rw [hcast] at h1
    have h2 : (((2 * x).sqrt : ℕ) : ℝ) ^ 2 ≤ (2 * Real.sqrt (x : ℝ)) ^ 2 := by
      nlinarith [h1, hsq, hx0]
    have h3 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq hs0, Real.sqrt_sq (by positivity)] at h3
    have h4 : (4 : ℝ) * Real.sqrt (x : ℝ) ≤ paperTheorem16LogSqConstant * Real.sqrt (x : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hr0
    linarith
  -- Third term: `⌊x/y⌋(1 + log⌊x/y⌋) ≤ (x/y)(1 + log x) ≤ 5 x log x / y ≤ C x log x / y`.
  have hrhs0 : (0 : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) / (y : ℝ) :=
    div_nonneg (mul_nonneg hx0 hlogx) hy0.le
  have hT3 : ((x / y : ℕ) : ℝ) * (1 + Real.log ((x / y : ℕ) : ℝ)) ≤
      paperTheorem16LogSqConstant * ((x : ℝ) * Real.log (x : ℝ) / (y : ℝ)) := by
    have hCrhs : (0 : ℝ) ≤ paperTheorem16LogSqConstant *
        ((x : ℝ) * Real.log (x : ℝ) / (y : ℝ)) := mul_nonneg (by linarith) hrhs0
    rcases Nat.eq_zero_or_pos (x / y) with hd0 | hdpos
    · rw [hd0]
      simp only [Nat.cast_zero, zero_mul]
      linarith
    · have hd1 : (1 : ℝ) ≤ ((x / y : ℕ) : ℝ) := by exact_mod_cast hdpos
      have hdlog : 0 ≤ Real.log ((x / y : ℕ) : ℝ) := Real.log_nonneg hd1
      have hdlex : ((x / y : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.div_le_self x y
      have hlogle : Real.log ((x / y : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by linarith) hdlex
      have hdle : ((x / y : ℕ) : ℝ) ≤ (x : ℝ) / (y : ℝ) := Nat.cast_div_le
      have step1 : ((x / y : ℕ) : ℝ) * (1 + Real.log ((x / y : ℕ) : ℝ)) ≤
          ((x : ℝ) / (y : ℝ)) * (1 + Real.log (x : ℝ)) :=
        mul_le_mul hdle (by linarith) (by linarith) hquot0
      have hguard : 1 + Real.log (x : ℝ) ≤ logGuardConstant * Real.log (x : ℝ) :=
        one_add_log_le_logGuardConstant_mul_log hx2
      have hg5 := mul_le_mul_of_nonneg_right logGuardConstant_le_five hlogx
      have step2 : ((x : ℝ) / (y : ℝ)) * (1 + Real.log (x : ℝ)) ≤
          ((x : ℝ) / (y : ℝ)) * (5 * Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hquot0
      have heq : ((x : ℝ) / (y : ℝ)) * (5 * Real.log (x : ℝ)) =
          5 * ((x : ℝ) * Real.log (x : ℝ) / (y : ℝ)) := by
        field_simp
      have step3 : (5 : ℝ) * ((x : ℝ) * Real.log (x : ℝ) / (y : ℝ)) ≤
          paperTheorem16LogSqConstant * ((x : ℝ) * Real.log (x : ℝ) / (y : ℝ)) :=
        mul_le_mul_of_nonneg_right hC5 hrhs0
      linarith [step1, step2, heq.le, heq.ge, step3]
  -- Fifth term: the divisor-weighted census sum is nonnegative, so `C ≥ 1` suffices.
  have hT5 : smoothMultiplierB4Sum x y ≤
      paperTheorem16LogSqConstant * smoothMultiplierB4Sum x y := by
    have hb := smoothMultiplierB4Sum_nonneg x y
    nlinarith [hC5, hb]
  unfold paperTransferDisplay
  have hT4 : paperTheorem16LogSqConstant * (x : ℝ) * Real.log (y : ℝ) ^ 2 * (y : ℝ)⁻¹ =
      paperTheorem16LogSqConstant * ((x : ℝ) * Real.log (y : ℝ) ^ 2 / (y : ℝ)) := by
    rw [div_eq_mul_inv]
    ring
  linarith [hT1, hT2, hT3, hT4.le, hT4.ge, hT5]

/-! ## The off-diagonal remainder at an arbitrary shift -/

/-! ## The second display, and the two-sided form -/

end

end RankAmplification
