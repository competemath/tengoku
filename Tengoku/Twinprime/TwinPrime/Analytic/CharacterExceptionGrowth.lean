import Tengoku.Twinprime.TwinPrime.Analytic.CharacterExceptions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absorbing the accumulated character replacement error

The elementary principal-character exception bound is small enough at the
Bombieri--Vinogradov modulus range. Increasing the logarithmic cutoff exponent
from `A` to `A + 2` absorbs the full error, uniformly over the modulus bound
and over independently chosen summation endpoints. No prime-distribution
estimate is used.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def characterExceptionBudget (X Q : ℕ) : ℝ :=
  Q * (Real.log Q + 2 * Real.sqrt (2 * X + 2) * Real.log (2 * X + 2))

theorem characterExceptionBudget_le (X Q : ℕ) (hX : 2 ≤ X) (hQ : Q ≤ X) :
    characterExceptionBudget X Q ≤ 13 * Q * Real.sqrt X * Real.log X := by
  rcases Q.eq_zero_or_pos with rfl | hQ0
  · simp [characterExceptionBudget]
  have hx : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) ≤ X := by positivity
  have hl : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  have hlt0 : 0 ≤ Real.log (2 * X + 2 : ℝ) := Real.log_nonneg (by linarith)
  have hs1 : 1 ≤ Real.sqrt (X : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hsq := Real.sq_sqrt hx0
  have hs : Real.sqrt (2 * X + 2 : ℝ) ≤ 2 * Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hcube : (2 * X + 2 : ℝ) ≤ (X : ℝ) ^ 3 := by
    have h4 : (4 : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr h4)]
  have hlt : Real.log (2 * X + 2 : ℝ) ≤ 3 * Real.log X := by
    calc
      _ ≤ Real.log ((X : ℝ) ^ 3) := Real.log_le_log (by positivity) hcube
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlq : Real.log (Q : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hQ0) (by exact_mod_cast hQ)
  have hinside : Real.log (Q : ℝ) + 2 * Real.sqrt (2 * X + 2) *
      Real.log (2 * X + 2) ≤ 13 * Real.sqrt X * Real.log X := by
    calc
      _ ≤ Real.log X + 2 * (2 * Real.sqrt X) * (3 * Real.log X) := by
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hl]
  exact (mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg Q)).trans_eq (by ring)

/-- The logarithmic cutoff exponent is explicit, and the final constant is one.-/
theorem characterExceptionBudget_le_log_saving (A : ℝ) (hA : 0 < A)
    (X Q : ℕ) (hX : 2 ≤ X) (hlog : 13 ≤ Real.log (X : ℝ))
    (hQ : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2)) :
    characterExceptionBudget X Q ≤ (X : ℝ) / (Real.log X) ^ A := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hx0 : (0 : ℝ) ≤ X := by positivity
  have hl : 0 < Real.log (X : ℝ) := by linarith
  have hp : 0 < (Real.log (X : ℝ)) ^ (A + 2) := Real.rpow_pos_of_pos hl _
  have hpA : 0 < (Real.log (X : ℝ)) ^ A := Real.rpow_pos_of_pos hl _
  have hp1 : 1 ≤ (Real.log (X : ℝ)) ^ (A + 2) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hQ' : (Q : ℝ) ≤ Real.sqrt X / (Real.log X) ^ (A + 2) := by
    simpa only [Real.sqrt_eq_rpow] using hQ
  have hQX : Q ≤ X := by
    have hdiv : Real.sqrt (X : ℝ) / (Real.log X) ^ (A + 2) ≤ Real.sqrt X := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg (Real.sqrt_nonneg (X : ℝ)) (sub_nonneg.mpr hp1)]
    exact_mod_cast hQ'.trans (hdiv.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx)))
  have hpow : (Real.log (X : ℝ)) ^ (A + 2) =
      (Real.log X) ^ A * (Real.log X) ^ (2 : ℕ) := by
    rw [Real.rpow_add hl, Real.rpow_two]
  have hratio : 13 / Real.log (X : ℝ) ≤ 1 := (div_le_one hl).mpr hlog
  calc
    _ ≤ 13 * Q * Real.sqrt X * Real.log X := characterExceptionBudget_le X Q hX hQX
    _ ≤ 13 * (Real.sqrt X / (Real.log X) ^ (A + 2)) * Real.sqrt X * Real.log X := by
      gcongr
    _ = (13 / Real.log X) * ((Real.sqrt X) ^ 2 / (Real.log X) ^ A) := by
      rw [hpow]
      field_simp
    _ = (13 / Real.log X) * ((X : ℝ) / (Real.log X) ^ A) := by rw [Real.sq_sqrt hx0]
    _ ≤ 1 * ((X : ℝ) / (Real.log X) ^ A) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := one_mul _

theorem eventually_characterExceptionBudget_le (A : ℝ) (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2) →
      characterExceptionBudget X Q ≤ (X : ℝ) / (Real.log X) ^ A := by
  have hlog : ∀ᶠ X : ℕ in atTop, 13 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 13)
  filter_upwards [eventually_ge_atTop 2, hlog] with X hX hl Q hQ
  exact characterExceptionBudget_le_log_saving A hA X Q hX hl hQ

theorem exists_exponent_characterExceptionBudget_le (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ B →
      characterExceptionBudget X Q ≤ (X : ℝ) / (Real.log X) ^ A :=
  ⟨A + 2, by linarith, eventually_characterExceptionBudget_le A hA⟩

/-- Every modulus may choose its own endpoint through `2X+2`.-/
theorem sum_noncoprimeMangoldtMass_le_characterExceptionBudget (X Q : ℕ)
    (t : ℕ → ℕ) (ht : ∀ q ∈ Ioc 0 Q, t q ≤ 2 * X + 2) :
    (∑ q ∈ Ioc 0 Q, noncoprimeMangoldtMass (t q) q) ≤
      characterExceptionBudget X Q := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, characterExceptionBudget] using
    sum_noncoprimeMangoldtMass_le_uniform (2 * X + 2) Q (by omega) t ht

theorem eventually_sum_noncoprimeMangoldtMass_le (A : ℝ) (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2) →
      ∀ t : ℕ → ℕ, (∀ q ∈ Ioc 0 Q, t q ≤ 2 * X + 2) →
      (∑ q ∈ Ioc 0 Q, noncoprimeMangoldtMass (t q) q) ≤
        (X : ℝ) / (Real.log X) ^ A := by
  filter_upwards [eventually_characterExceptionBudget_le A hA] with X hX Q hQ t ht
  exact (sum_noncoprimeMangoldtMass_le_characterExceptionBudget X Q t ht).trans (hX Q hQ)

end TwinPrime.Analytic
