import Tengoku.Rankamplificationtotient.RankAmplification.Section4Assembly
import Tengoku.Rankamplificationtotient.RankAmplification.Section4ReciprocalSharp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Premise-free wrappers for numbered paper statements This module exposes paper-facing forms of numbered results whose generic assembly theorem accepts an abstract finite majorant, while another checked module constructs that majorant canonically. -/

namespace RankAmplification

noncomputable section

/-- Lemma 2.8 in its paper-facing rational-quotient form: equality of the Euler totient factors forces equality of prime support.
@isnad1 id=eq.3h2v.s6.1cd387f53c15 from=translated src=- shape=bb7f7bc2 vocab=37d47252
-/
theorem lemma2_9_primeSupport_eq_of_totient_div_eq
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hratio : (a.totient : ℚ) / a = (b.totient : ℚ) / b) :
    primeSupport a = primeSupport b := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hcrossQ : (a.totient : ℚ) * (b : ℚ) =
      (b.totient : ℚ) * (a : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr ha0)
      (Nat.cast_ne_zero.mpr hb0)).mp hratio
  apply primeSupport_eq_of_totient_cross_eq ha0 hb0
  exact_mod_cast hcrossQ

/-! ### Removing the guard: `(1 + log y)^2 ≍ (log y)^2` for `y ≥ 2` -/

/-- The explicit absolute constant `(1 + log 2)/log 2 = 2.4426…` converting the guarded logarithm `1 + log y` into the paper's bare `log y` on the whole range `y ≥ 2`.-/
def logGuardConstant : ℝ := (1 + Real.log 2) / Real.log 2

/--
@isnad1 id=le.0h0v.s3.e1de86ef8171 from=translated src=- shape=ff3a10fc vocab=74346cab
-/
theorem logGuardConstant_nonneg : 0 ≤ logGuardConstant := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold logGuardConstant
  positivity

/-- Upper half of `1 + log y ≍ log y` on `y ≥ 2`: the guard costs only the absolute factor `logGuardConstant`.
@isnad1 id=le.1h1v.s5.ac9a01ac66b9 from=translated src=- shape=ca894ee3 vocab=a56ac1e3
-/
theorem one_add_log_le_logGuardConstant_mul_log {y : ℕ} (hy : 2 ≤ y) :
    1 + Real.log y ≤ logGuardConstant * Real.log y := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  unfold logGuardConstant
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  nlinarith [hL, h2]

/-- Lower half of `1 + log y ≍ log y` on `y ≥ 2`, with constant `1`: the guarded logarithm is never smaller than the bare one.
@isnad1 id=le.1h1v.s6.e22950340f56 from=translated src=- shape=cde930de vocab=fe6e0b48
-/
theorem log_sq_le_one_add_log_sq {y : ℕ} (hy : 2 ≤ y) :
    Real.log y ^ 2 ≤ (1 + Real.log y) ^ 2 := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.one_le_of_lt hy
  have hL : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hy1
  nlinarith [hL]

/-- The squared form of `one_add_log_le_logGuardConstant_mul_log`.
@isnad1 id=le.1h1v.s6.1e4d9a926810 from=translated src=- shape=42ab978c vocab=c8b4f1dc
-/
theorem one_add_log_sq_le_logGuardConstant_sq_mul_log_sq {y : ℕ} (hy : 2 ≤ y) :
    (1 + Real.log y) ^ 2 ≤ logGuardConstant ^ 2 * Real.log y ^ 2 := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.one_le_of_lt hy
  have hnn : (0 : ℝ) ≤ 1 + Real.log (y : ℝ) := by
    have := Real.log_nonneg hy1
    linarith
  have h := one_add_log_le_logGuardConstant_mul_log hy
  have hsq : (1 + Real.log (y : ℝ)) * (1 + Real.log (y : ℝ)) ≤
      (logGuardConstant * Real.log y) * (logGuardConstant * Real.log y) :=
    mul_le_mul h h hnn (hnn.trans h)
  nlinarith [hsq]

/-- The explicit absolute constant `5 · 4^8 · ((1 + log 2)/log 2)^2 = 1.955… × 10^6` in the fourth term of the paper's display (1.6).-/
def paperTheorem16LogSqConstant : ℝ := section4SharpConstant * logGuardConstant ^ 2

/--
@isnad1 id=le.0h0v.s3.16ffbc5418db from=translated src=- shape=ff3a10fc vocab=f755c46c
-/
theorem paperTheorem16LogSqConstant_nonneg : 0 ≤ paperTheorem16LogSqConstant := by
  unfold paperTheorem16LogSqConstant
  exact mul_nonneg section4SharpConstant_nonneg (sq_nonneg _)

/-! ### Theorem 1.6 with a single absolute implied constant on the paper's five terms -/

/-- The right-hand side of the paper's display (1.6) *before* the implied constant: `x/y + x^{1/2} + x log x / y + x (log y)^2 / y + ∑_{y<p≤(2xy)^{1/2}} Ψ_τ(2xy/p², p)`.-/
def paperTransferDisplay (x y : ℕ) : ℝ :=
  (x : ℝ) / y + Real.sqrt x + (x : ℝ) * Real.log x / y +
    (x : ℝ) * Real.log y ^ 2 / y + smoothMultiplierB4Sum x y

/--
@isnad1 id=le.0h2v.s4.f058c634f650 from=translated src=- shape=5ffe46ab vocab=f190f3fc
-/
theorem smoothMultiplierB4Sum_nonneg (x y : ℕ) : 0 ≤ smoothMultiplierB4Sum x y := by
  unfold smoothMultiplierB4Sum
  refine Finset.sum_nonneg fun p _ ↦ ?_
  rw [finiteDivisorWeightedSmoothCount_eq]
  exact Finset.sum_nonneg fun m _ ↦ Nat.cast_nonneg _

/--
@isnad1 id=le.0h0v.s3.d93a7335a871 from=translated src=- shape=ff3a10fc vocab=74346cab
-/
theorem one_le_logGuardConstant : 1 ≤ logGuardConstant := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold logGuardConstant
  rw [le_div_iff₀ h2]
  linarith

/--
@isnad1 id=le.0h0v.s3.42e9278647b7 from=translated src=- shape=ffdda526 vocab=ebe48c24
-/
theorem logGuardConstant_le_five : logGuardConstant ≤ 5 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2pos : (0 : ℝ) < Real.log 2 := by linarith
  unfold logGuardConstant
  rw [div_le_iff₀ h2pos]
  linarith

/--
@isnad1 id=le.0h0v.s3.43fa1c8efd84 from=translated src=- shape=ff3a10fc vocab=ecff1d3b
-/
theorem five_le_section4SharpConstant : 5 ≤ section4SharpConstant := by
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h : (1 : ℝ) ≤ Real.exp (4 * Real.log 4) := Real.one_le_exp (by linarith)
  unfold section4SharpConstant
  nlinarith [h]

/--
@isnad1 id=le.0h0v.s3.b1bc34032304 from=translated src=- shape=ff3a10fc vocab=017d4e73
-/
theorem five_le_paperTheorem16LogSqConstant : 5 ≤ paperTheorem16LogSqConstant := by
  have hS := five_le_section4SharpConstant
  have hg := one_le_logGuardConstant
  unfold paperTheorem16LogSqConstant
  nlinarith [hS, hg, sq_nonneg logGuardConstant]

/-- Proposition 9.7, equation (9.4): the displayed diagonal is contained in the nonsmooth solution set, and subtraction leaves exactly the off-diagonal remainder.
@isnad1 id=and.0h3v.s5.e33964967b88 from=translated src=- shape=c7e2bbe0 vocab=02b8ca84
-/
theorem proposition9_6_exact_cardinality_unconditional
    (x h y : ℕ) :
    aboveCutoffDiagonalCount x h y ≤ nonsmoothShiftedCount x h y ∧
      nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y =
        offDiagonalNonsmoothCount x h y := by
  exact ⟨aboveCutoffDiagonalCount_le_nonsmoothShiftedCount x h y,
    nonsmoothShiftedCount_sub_aboveCutoffDiagonalCount x h y⟩

end

end RankAmplification
