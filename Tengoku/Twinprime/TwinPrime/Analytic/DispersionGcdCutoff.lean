import Tengoku.Twinprime.TwinPrime.Analytic.BVLogComparisons

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A logarithmic gcd cutoff for the growing dyadic family

The ceiling of the tenth power of the dispersion logarithm absorbs the
per-box fourth logarithmic power and the square of the dyadic depth. All
estimates in this file are numerical; no off-diagonal estimate is assumed
except as the explicit input to the final transfer theorem.
-/

noncomputable section

open Filter
open scoped Topology

namespace TwinPrime.Analytic

def dispersionGcdCutoff (X : ℕ) : ℕ := ⌈(Real.log (4 * (X : ℝ) + 4)) ^ 10⌉₊

theorem one_le_dispersion_log (X : ℕ) : 1 ≤ Real.log (4 * (X : ℝ) + 4) := by
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hle : Real.log (4 : ℝ) ≤ Real.log (4 * (X : ℝ) + 4) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  linarith [half_le_log_two]

theorem log_pow_le_dispersionGcdCutoff (X : ℕ) :
    (Real.log (4 * (X : ℝ) + 4)) ^ 10 ≤ (dispersionGcdCutoff X : ℝ) :=
  Nat.le_ceil _

theorem one_le_dispersionGcdCutoff (X : ℕ) : 1 ≤ dispersionGcdCutoff X := by
  have h : (1 : ℝ) ≤ (dispersionGcdCutoff X : ℝ) :=
    (one_le_pow₀ (one_le_dispersion_log X)).trans (log_pow_le_dispersionGcdCutoff X)
  exact_mod_cast h

theorem dispersionGcdCutoff_le_two_log_pow (X : ℕ) :
    (dispersionGcdCutoff X : ℝ) ≤ 2 * (Real.log (4 * (X : ℝ) + 4)) ^ 10 := by
  have hp : (1 : ℝ) ≤ (Real.log (4 * (X : ℝ) + 4)) ^ 10 :=
    one_le_pow₀ (one_le_dispersion_log X)
  exact Nat.ceil_le_two_mul (by norm_num; linarith)

/-- The ceiling costs nothing in the useful direction for the error.-/
theorem sqrt_dispersionGcdCutoff_error_le (X : ℕ) :
    Real.sqrt (16 * (Real.log (4 * (X : ℝ) + 4)) ^ 4 / dispersionGcdCutoff X) ≤
      4 / (Real.log (4 * (X : ℝ) + 4)) ^ 3 := by
  let L : ℝ := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hG : (0 : ℝ) < dispersionGcdCutoff X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_dispersionGcdCutoff X))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hG).mpr
  have h := mul_le_mul_of_nonneg_left (log_pow_le_dispersionGcdCutoff X)
    (sq_nonneg (4 / L ^ 3))
  have heq : (4 / L ^ 3) ^ 2 * L ^ 10 = 16 * L ^ 4 := by
    field_simp
    ring
  exact heq.symm.trans_le h

/-- The actual dyadic depth at `2X` is bounded using the same logarithm
as the cutoff. The fixed threshold makes the earlier depth estimate apply.-/
theorem dyadicNatDepth_two_mul_le_dispersion_log (X : ℕ) (hX : 128 ≤ X) :
    (dyadicNatDepth (2 * X) : ℝ) ≤
      (2 / Real.log 2) * Real.log (4 * (X : ℝ) + 4) := by
  have hlog2 : 0 < Real.log 2 := by linarith [half_le_log_two]
  have hlog : Real.log ((2 * X : ℕ) : ℝ) ≤ Real.log (4 * (X : ℝ) + 4) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < 2 * X by omega)
    · push_cast
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
  exact (dyadicNatDepth_le_two_div_log_two_mul_log (2 * X) (by omega)).trans
    (mul_le_mul_of_nonneg_left hlog (by positivity))

/-- The complete growing-family budget loses only one reciprocal logarithm.-/
theorem dispersionGcdCutoff_family_error_le (X : ℕ) (hX : 128 ≤ X) :
    (dyadicNatDepth (2 * X) : ℝ) ^ 2 *
      Real.sqrt (16 * (Real.log (4 * (X : ℝ) + 4)) ^ 4 / dispersionGcdCutoff X) ≤
        4 * (2 / Real.log 2) ^ 2 / Real.log (4 * (X : ℝ) + 4) := by
  let L : ℝ := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hD := dyadicNatDepth_two_mul_le_dispersion_log X hX
  have hDsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (dyadicNatDepth (2 * X))) hD 2
  calc
    _ ≤ ((2 / Real.log 2) * L) ^ 2 * (4 / L ^ 3) :=
      mul_le_mul hDsq (sqrt_dispersionGcdCutoff_error_le X)
        (Real.sqrt_nonneg _) (sq_nonneg _)
    _ = _ := by
      change ((2 / Real.log 2) * L) ^ 2 * (4 / L ^ 3) = 4 * (2 / Real.log 2) ^ 2 / L
      field_simp

theorem tendsto_dispersionGcdCutoff_family_error :
    Tendsto (fun X : ℕ => (dyadicNatDepth (2 * X) : ℝ) ^ 2 *
      Real.sqrt (16 * (Real.log (4 * (X : ℝ) + 4)) ^ 4 / dispersionGcdCutoff X))
      atTop (𝓝 0) := by
  have harg : Tendsto (fun X : ℕ => 4 * (X : ℝ) + 4) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)
  have hupper : Tendsto (fun X : ℕ =>
      4 * (2 / Real.log 2) ^ 2 / Real.log (4 * (X : ℝ) + 4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      hinv.const_mul (4 * (2 / Real.log 2) ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with X
    exact mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 128] with X hX
    exact dispersionGcdCutoff_family_error_le X hX

/-- Any nonnegative actual error satisfying the displayed full-family
budget is sublinear. The bound may hold only eventually.-/
theorem tendsto_div_of_dispersionGcdCutoff_bound (F : ℕ → ℝ)
    (hF : ∀ᶠ X : ℕ in atTop, 0 ≤ F X)
    (hbound : ∀ᶠ X : ℕ in atTop,
      F X / X ≤ (dyadicNatDepth (2 * X) : ℝ) ^ 2 *
        Real.sqrt (16 * (Real.log (4 * (X : ℝ) + 4)) ^ 4 / dispersionGcdCutoff X)) :
    Tendsto (fun X : ℕ => F X / X) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_dispersionGcdCutoff_family_error
  · filter_upwards [hF] with X hX
    exact div_nonneg hX (Nat.cast_nonneg X)
  · exact hbound

end TwinPrime.Analytic
