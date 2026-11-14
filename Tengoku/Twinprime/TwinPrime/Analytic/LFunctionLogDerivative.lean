import Tengoku.Seed.NumberTheory.LSeries.Dirichlet
import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic derivatives in the half-plane of absolute convergence

The analytically continued Dirichlet L-function has its usual von Mangoldt
logarithmic derivative on `re s > 1`. Its norm is bounded by the real,
nonnegative negative logarithmic derivative of zeta at `re s`. These facts
include principal characters and modulus one and use no distribution input.
The three-four-one derivative inequality follows from coefficient positivity
and absolute convergence, retaining the full zeta contribution.
-/

noncomputable section

open ArithmeticFunction Complex

namespace TwinPrime.Analytic

/-- The positive real majorant for logarithmic derivatives.-/
def mangoldtDirichletMass (σ : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ σ

/--
@isnad1 id=le.0h1v.s3.501bc688e5f7 from=translated src=- shape=8a62b088 vocab=a6ecba4b
-/
theorem mangoldtDirichletMass_nonneg (σ : ℝ) : 0 ≤ mangoldtDirichletMass σ :=
  tsum_nonneg fun _ => div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/--
@isnad1 id=eq.0h2v.s5.4d921c84e414 from=translated src=- shape=f3acfca1 vocab=4c43e265
-/
theorem vonMangoldt_term_real (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) (σ : ℂ) n =
      ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero (by omega), Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/--
@isnad1 id=eq.0h1v.s4.e2aca137c8fc from=translated src=- shape=9d6eaa83 vocab=2b55d42f
-/
theorem LSeries_vonMangoldt_real_eq (σ : ℝ) :
    LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) (σ : ℂ) =
      (mangoldtDirichletMass σ : ℂ) := by
  unfold LSeries mangoldtDirichletMass
  rw [Complex.ofReal_tsum]
  exact tsum_congr (vonMangoldt_term_real σ)

/--
@isnad1 id=summable.1h1v.s5.5d897189a249 from=translated src=- shape=359a0925 vocab=3293d5c6
-/
theorem summable_mangoldtDirichletMass {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ σ) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)
  exact Complex.summable_ofReal.mp (h.congr (vonMangoldt_term_real σ))

/-- The majorant is precisely the negative zeta logarithmic derivative.
@isnad1 id=eq.1h1v.s6.9302d8e3e814 from=translated src=- shape=f7b1b8fa vocab=ee58ea4f
-/
theorem neg_zeta_logDerivative_eq_mass {σ : ℝ} (hσ : 1 < σ) :
    -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) =
      (mangoldtDirichletMass σ : ℂ) :=
  (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by simpa using hσ)).symm.trans (LSeries_vonMangoldt_real_eq σ)

/--
@isnad1 id=le.1h1v.s6.2d085cb4cf93 from=translated src=- shape=72bab61b vocab=4c9372af
-/
theorem neg_zeta_logDerivative_re_nonneg {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  rw [neg_zeta_logDerivative_eq_mass hσ, Complex.ofReal_re]
  exact mangoldtDirichletMass_nonneg σ

/--
@isnad1 id=eq.1h1v.s6.b7ccc44100df from=translated src=- shape=68ecd92e vocab=9f5c04ed
-/
theorem neg_zeta_logDerivative_im_eq_zero {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).im = 0 := by
  rw [neg_zeta_logDerivative_eq_mass hσ, Complex.ofReal_im]

/-- The derivative belongs to the analytic continuation, not merely the series.
@isnad1 id=eq.1h3v.s7.e099f77fce7e from=translated src=- shape=a7954606 vocab=dfc23690
-/
theorem neg_LFunction_logDerivative_eq_twist {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      LSeries (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact (DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs).symm

/--
@isnad1 id=le.0h4v.s7.a65446cf0954 from=translated src=- shape=bc329dc6 vocab=48eb8569
-/
theorem norm_twist_vonMangoldt_term_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) s n‖ ≤
      vonMangoldt n / (n : ℝ) ^ s.re := by
  rw [LSeries.norm_term_eq]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [ite_eq_right (by omega), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

/-- Absolute convergence gives a scalar majorant independent of the character
and imaginary part.
@isnad1 id=le.1h3v.s6.fcf03ce68bf0 from=translated src=- shape=3459286d vocab=e010683c
-/
theorem norm_twist_vonMangoldt_LSeries_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) s‖ ≤
      mangoldtDirichletMass s.re := by
  have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  apply (norm_tsum_le_tsum_norm h.norm).trans
  exact Summable.tsum_le_tsum (norm_twist_vonMangoldt_term_le χ s) h.norm
    (summable_mangoldtDirichletMass hs)

/-- The standard zeta bound for every Dirichlet logarithmic derivative,
including principal characters and modulus one.
@isnad1 id=le.1h3v.s7.f641f0cc774d from=translated src=- shape=ba346405 vocab=81ca6d73
-/
theorem norm_LFunction_logDerivative_le_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  rw [neg_zeta_logDerivative_eq_mass hs, Complex.ofReal_re]
  have h := norm_twist_vonMangoldt_LSeries_le χ hs
  rw [← neg_LFunction_logDerivative_eq_twist χ hs, neg_div, norm_neg] at h
  exact h

/-- The coefficient inequality underlying the classical three-four-one argument.
@isnad1 id=le.1h1v.s6.db41c9dc6e94 from=translated src=- shape=de9e1df2 vocab=38325dc8
-/
theorem three_four_one_re_nonneg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnorm : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have hsq := Complex.sq_norm z
    rw [Complex.normSq_apply] at hsq
    nlinarith [norm_nonneg z]
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

/-- Separate the positive real weight from the character and imaginary phase.
@isnad1 id=eq.1h5v.s7.8f723113f234 from=translated src=- shape=be506b4c vocab=6adfac26
-/
theorem twist_vonMangoldt_term_eq_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun n : ℕ => χ n * (vonMangoldt n : ℂ))
        ((σ : ℂ) + I * t) n =
      ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) *
        (χ n * (n : ℂ) ^ (-(I * t))) := by
  rw [LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ (by exact_mod_cast hn), Complex.cpow_neg,
    Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/--
@isnad1 id=le.1h4v.s6.a59bc4cffcea from=translated src=- shape=3ff08318 vocab=289545e5
-/
theorem character_cpow_phase_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖χ n * (n : ℂ) ^ (-(I * t))‖ ≤ 1 := by
  have hphase : ‖(n : ℂ) ^ (-(I * t))‖ = 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    simp
  simpa only [norm_mul, hphase, mul_one] using χ.norm_le_one (n : ZMod q)

/--
@isnad1 id=eq.0h4v.s8.8e788e6ec608 from=translated src=- shape=1d0f3235 vocab=1156fb60
-/
theorem character_cpow_phase_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) :
    (χ ^ 2) n * (n : ℂ) ^ (-(I * ((2 * t : ℝ) : ℂ))) =
      (χ n * (n : ℂ) ^ (-(I * t))) ^ 2 := by
  rw [χ.pow_apply' two_ne_zero,
    show -(I * ((2 * t : ℝ) : ℂ)) = (2 : ℕ) * (-(I * t)) by push_cast; ring,
    Complex.cpow_nat_mul, mul_pow]

/-- Coefficientwise three-four-one positivity, including zero coefficients
at integers not coprime to the modulus.
@isnad1 id=le.0h5v.s8.40b1555616b9 from=translated src=- shape=6c33e054 vocab=ee4e26e0
-/
theorem three_four_one_vonMangoldt_term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (vonMangoldt n / (n : ℝ) ^ σ) +
      4 * (LSeries.term (fun n : ℕ => χ n * (vonMangoldt n : ℂ))
        ((σ : ℂ) + I * t) n).re +
      (LSeries.term (fun n : ℕ => (χ ^ 2) n * (vonMangoldt n : ℂ))
        ((σ : ℂ) + I * (2 * t : ℝ)) n).re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [twist_vonMangoldt_term_eq_phase χ σ t (by omega),
    twist_vonMangoldt_term_eq_phase (χ ^ 2) σ (2 * t) (by omega),
    character_cpow_phase_sq χ t n]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := mul_nonneg
    (div_nonneg (vonMangoldt_nonneg (n := n)) (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
    (three_four_one_re_nonneg _ (character_cpow_phase_norm_le_one χ t hn))
  simp only [Complex.mul_re] at h
  nlinarith

/-- The three-four-one inequality for absolutely convergent twisted series.
@isnad1 id=le.1h4v.s8.60983bbde00d from=translated src=- shape=9479843b vocab=6a098ec9
-/
theorem three_four_one_vonMangoldt_LSeries_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * mangoldtDirichletMass σ +
      4 * (LSeries (fun n : ℕ => χ n * (vonMangoldt n : ℂ))
        ((σ : ℂ) + I * t)).re +
      (LSeries (fun n : ℕ => (χ ^ 2) n * (vonMangoldt n : ℂ))
        ((σ : ℂ) + I * (2 * t : ℝ))).re := by
  have h1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have h2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2)
    (s := (σ : ℂ) + I * (2 * t : ℝ)) (by simpa using hσ)
  have hsum := (((summable_mangoldtDirichletMass hσ).hasSum.mul_left 3).add
    ((Complex.hasSum_re h1.hasSum).mul_left 4)).add (Complex.hasSum_re h2.hasSum)
  exact le_hasSum_of_le_sum hsum (fun S => Finset.sum_nonneg fun n _ =>
    three_four_one_vonMangoldt_term_nonneg χ σ t n)

/-- Actual logarithmic-derivative positivity in the half-plane `σ>1`.
The first term is zeta, so the statement also covers integers not coprime
to the character modulus without a missing Euler-factor correction.
@isnad1 id=le.1h4v.s9.80a0222aa6bd from=translated src=- shape=2bf621a7 vocab=5ff6b5f5
-/
theorem three_four_one_LFunction_logDerivative_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * t) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + I * t)).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2)) ((σ : ℂ) + I * (2 * t : ℝ)) /
        DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + I * (2 * t : ℝ))).re := by
  rw [neg_zeta_logDerivative_eq_mass hσ, Complex.ofReal_re,
    neg_LFunction_logDerivative_eq_twist χ (by simpa using hσ),
    neg_LFunction_logDerivative_eq_twist (χ ^ 2) (by simpa using hσ)]
  exact three_four_one_vonMangoldt_LSeries_nonneg χ hσ t

end TwinPrime.Analytic
