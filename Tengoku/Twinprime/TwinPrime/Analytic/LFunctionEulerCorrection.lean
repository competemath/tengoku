import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.Seed.Analysis.Calculus.LogDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Logarithmic derivatives of induced Dirichlet L-functions

The exact change-of-modulus identity is differentiated with all Euler
denominators justified.  The resulting finite correction has norm at most
the logarithm of the larger positive modulus on `1 < s.re`.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- The finite correction uses the prime factors of the larger modulus.-/
def characterEulerCorrection {M : ℕ} (χ : DirichletCharacter ℂ M)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ N.primeFactors,
    χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - χ p * (p : ℂ) ^ (-s))

/--
@isnad1 id=eq.0h3v.s5.7ff855519a11 from=translated src=- shape=0e11a4ed vocab=81e35609
-/
@[simp] theorem characterEulerCorrection_one {M : ℕ}
    (χ : DirichletCharacter ℂ M) (s : ℂ) : characterEulerCorrection χ 1 s = 0 := by
  simp [characterEulerCorrection]

/-- A uniform smallness bound for every prime Euler ratio.
@isnad1 id=le.2h4v.s7.7664ab6d050d from=translated src=- shape=8ef92cb5 vocab=2c2f32a3
-/
theorem norm_characterEulerRatio_le_half {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  calc
    _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-s.re) := one_mul _
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hs)
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2

/-- Euler denominators are nonzero already on the boundary `s.re=1`.
@isnad1 id=ne.2h4v.s7.2cffcd137624 from=translated src=- shape=8107f730 vocab=e09e1582
-/
theorem characterEulerFactor_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have h := norm_characterEulerRatio_le_half χ p hp s hs
  intro heq
  have hz : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -heq
  rw [hz, norm_one] at h
  norm_num at h

/-- Differentiation of one Euler factor with the real prime logarithm.
@isnad1 id=hasderiv.1h4v.s7.a035e8cf0be2 from=translated src=- shape=513db706 vocab=b4338252
-/
theorem hasDerivAt_characterEulerFactor {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 0 < p) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z))
      (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := (((hasDerivAt_id s).neg.const_cpow (c := (p : ℂ))
    (Or.inl hp0)).const_mul (χ p)).const_sub (1 : ℂ)
  simpa only [id_eq, Pi.neg_apply, ← Complex.natCast_log, neg_mul, mul_neg,
    mul_one, one_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using h

/-- Each Euler logarithmic-derivative term is bounded by the prime logarithm.
@isnad1 id=le.2h4v.s7.f462d3d7ccf4 from=translated src=- shape=8a7fe354 vocab=2f31f067
-/
theorem norm_characterEulerTerm_le_log {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) /
        (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ Real.log p := by
  let z : ℂ := χ p * (p : ℂ) ^ (-s)
  have hz : ‖z‖ ≤ 1 / 2 := norm_characterEulerRatio_le_half χ p hp s hs
  have hd : 1 / 2 ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hdpos : 0 < ‖1 - z‖ := by linarith
  have hn : ‖z‖ ≤ ‖1 - z‖ := hz.trans hd
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have heq : χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) = z * (Real.log p : ℂ) := by
    dsimp [z]
    ring
  rw [heq]
  change ‖z * (Real.log p : ℂ) / (1 - z)‖ ≤ Real.log p
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  apply (div_le_iff₀ hdpos).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn hlog]

/-- The logarithms of the distinct prime factors are bounded by that of
their positive parent modulus.  Modulus one has an empty sum.
@isnad1 id=le.1h1v.s5.5405e515580e from=translated src=- shape=e5169e03 vocab=6b19f6f1
-/
theorem sum_log_primeFactors_le_log (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ N.primeFactors, Real.log p) ≤ Real.log N := by
  have hp (p : ℕ) (hp : p ∈ N.primeFactors) : (0 : ℝ) < p := by
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)

/-- A finite, conductor-uniform bound for the entire inducing correction.
@isnad1 id=le.2h4v.s5.121bbd19ee9c from=translated src=- shape=41f47806 vocab=61b87341
-/
theorem norm_characterEulerCorrection_le_log {M : ℕ} (χ : DirichletCharacter ℂ M)
    (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖characterEulerCorrection χ N s‖ ≤ Real.log N := by
  unfold characterEulerCorrection
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum fun p hp => norm_characterEulerTerm_le_log χ p
    (Nat.prime_of_mem_primeFactors hp).two_le s hs).trans
  exact sum_log_primeFactors_le_log N hN

end TwinPrime.Analytic
