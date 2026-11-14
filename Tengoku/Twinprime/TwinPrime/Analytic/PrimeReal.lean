import Tengoku.Twinprime.TwinPrime.Analytic.BombieriVinogradovPsi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Passing the ordinary prime error from integer to real endpoints

The Chebyshev sum is constant between successive integers. Its main term is
not, and the resulting error of at most one is explicitly absorbed. The
logarithmic power is unchanged. No prime estimate is asserted unconditionally.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h1v.s5.66444c204ed5 from=translated src=- shape=0cb2de66 vocab=af79bc10
-/
theorem log_le_two_log_natFloor {x : ℝ} (hx : 4 ≤ x) :
    Real.log x ≤ 2 * Real.log (⌊x⌋₊ : ℝ) := by
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hnr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hfloor := Nat.lt_floor_add_one x
  have hx0 : 0 < x := by linarith
  have hsq : x ≤ (⌊x⌋₊ : ℝ) ^ 2 := by nlinarith
  calc
    Real.log x ≤ Real.log ((⌊x⌋₊ : ℝ) ^ 2) := Real.log_le_log hx0 hsq
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Every fixed logarithmic power is eventually at most the real scale.
@isnad1 id=eventual.0h1v.s4.98573ff9ff4a from=translated src=- shape=b88b1b9e vocab=b025f509
-/
theorem eventually_log_pow_le_self (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ k ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1) (by norm_num)).eventuallyLE
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x h hx
  simpa only [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_nonneg hx) k), abs_of_nonneg (by linarith : 0 ≤ x)] using h

/-- Integer Chebyshev errors imply the corresponding real-endpoint error,
with a displayed constant accounting for the floor and logarithm comparison.
@isnad1 id=eventual.2h2v.s7.d656a075710a from=translated src=- shape=6e669281 vocab=066d4d60
-/
theorem psi_real_error_of_nat_error (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hψ : ∀ᶠ N : ℕ in atTop,
      |Chebyshev.psi N - (N : ℝ)| ≤ K * N / (Real.log N) ^ k) :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ ((2 : ℝ) ^ k * K + 1) * x / (Real.log x) ^ k := by
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).eventually hψ
  filter_upwards [hfloor, eventually_ge_atTop (4 : ℝ), eventually_log_pow_le_self k]
    with x hψ hx hpow
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hnr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlogn : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hnle := Nat.floor_le hx0.le
  have hlogs : (Real.log x) ^ k ≤ (2 : ℝ) ^ k * (Real.log (⌊x⌋₊ : ℝ)) ^ k := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ hlogx.le (log_le_two_log_natFloor hx) k
  have hmain : K * (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ k ≤
      (2 : ℝ) ^ k * K * x / (Real.log x) ^ k := by
    apply (div_le_div_iff₀ (pow_pos hlogn k) (pow_pos hlogx k)).mpr
    calc
      K * (⌊x⌋₊ : ℝ) * (Real.log x) ^ k ≤
          K * x * ((2 : ℝ) ^ k * (Real.log (⌊x⌋₊ : ℝ)) ^ k) := by gcongr
      _ = _ := by ring
  have hone : (1 : ℝ) ≤ x / (Real.log x) ^ k :=
    (le_div_iff₀ (pow_pos hlogx k)).mpr (by simpa using hpow)
  calc
    |Chebyshev.psi x - x| ≤
        |Chebyshev.psi (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)| + |(⌊x⌋₊ : ℝ) - x| := by
      rw [Chebyshev.psi_eq_psi_coe_floor x]
      convert abs_add_le (Chebyshev.psi (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ))
        ((⌊x⌋₊ : ℝ) - x) using 1
      congr 1
      ring_nf
    _ ≤ K * (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ k + 1 :=
      add_le_add hψ (Nat.abs_floor_sub_le hx0.le)
    _ ≤ (2 : ℝ) ^ k * K * x / (Real.log x) ^ k + x / (Real.log x) ^ k :=
      add_le_add hmain hone
    _ = _ := by ring

/-- Modulus one of BV supplies the real prime estimate used by the centered
Selberg argument. The distribution theorem remains an explicit hypothesis.
@isnad1 id=ex.1h0v.s6.a1f60532d1eb from=translated src=- shape=d2fe5f53 vocab=22d68501
-/
theorem MaximalBombieriVinogradov.psi_real_log_six
    (hBV : MaximalBombieriVinogradov) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ K * x / (Real.log x) ^ 6 := by
  obtain ⟨K, hK, hψ⟩ := hBV.psi_error 6 (by norm_num)
  refine ⟨(2 : ℝ) ^ 6 * K + 1, by positivity, ?_⟩
  apply psi_real_error_of_nat_error 6 K hK.le
  simpa using hψ

end TwinPrime.Analytic
