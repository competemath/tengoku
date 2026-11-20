import Tengoku.Lmlf.LMLF.Definitions.Hypergeometric
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local Gauss hypergeometric differential equation

The ordinary and regularized Gauss hypergeometric series satisfy the unnormalized differential
equation on the open unit disk.  Keeping the equation in polynomial form includes both the
singular point `z = 0` and every exceptional denominator parameter of the regularized series.
-/

namespace LMLF.ODE

open LMLF.Definitions

private theorem regularizedGauss_coeff_recurrence
    (a b c : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) *
        (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      (a + n) * (b + n) *
        (Complex.regularizedGaussHGFunSeries a b c).coeff n := by
  rw [Complex.coeff_regularizedGaussHGFunSeries,
    Complex.coeff_regularizedGaussHGFunSeries,
    ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hgamma :=
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + (n : ℂ))
  simp only [div_eq_mul_inv, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev] at ⊢
  rw [show c + ((n : ℂ) + 1) = c + (n : ℂ) + 1 by ring]
  rw [hgamma]
  have hcancel : ((n : ℂ) + 1) * ((n : ℂ) + 1)⁻¹ = 1 := by
    apply mul_inv_cancel₀
    simpa using hn
  calc
    _ = (((n : ℂ) + 1) * ((n : ℂ) + 1)⁻¹) *
        ((a + n) * (b + n) *
          ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
            ((c + n) * (Complex.Gamma (c + n + 1))⁻¹ * (Nat.factorial n : ℂ)⁻¹))) := by
      ring
    _ = _ := by rw [hcancel, one_mul]

private theorem regularizedGauss_firstDerivative_hasFPowerSeriesOnBall (a b c : ℂ) :
    HasFPowerSeriesOnBall
      (deriv (regularizedGaussHypergeometricSeriesSum a b c))
      ((ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries
        (Complex.regularizedGaussHGFunSeries a b c).derivSeries) 0 1 := by
  have h := (ContinuousLinearMap.apply ℂ ℂ 1).comp_hasFPowerSeriesOnBall
    (regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall a b c).fderiv
  exact h.congr fun z _ ↦ by
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, deriv]

private theorem regularizedGauss_secondDerivative_hasFPowerSeriesOnBall (a b c : ℂ) :
    let p₁ := (ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries
      (Complex.regularizedGaussHGFunSeries a b c).derivSeries
    HasFPowerSeriesOnBall
      (deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)))
      ((ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries p₁.derivSeries) 0 1 := by
  dsimp only
  have h := (ContinuousLinearMap.apply ℂ ℂ 1).comp_hasFPowerSeriesOnBall
    (regularizedGauss_firstDerivative_hasFPowerSeriesOnBall a b c).fderiv
  exact h.congr fun z _ ↦ by
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, deriv]

/-- The regularized local Gauss series satisfies the unnormalized Gauss equation throughout the
open unit disk, including exceptional denominator parameters and the origin.-/
theorem regularizedGaussHypergeometricSeriesSum_gaussEquation
    {a b c z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) *
          deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z
      + (c - (a + b + 1) * z) *
          deriv (regularizedGaussHypergeometricSeriesSum a b c) z
      - a * b * regularizedGaussHypergeometricSeriesSum a b c z = 0 := by
  let A : ℕ → ℂ := fun n ↦
    (Complex.regularizedGaussHGFunSeries a b c).coeff n
  let p₁ := (ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries
    (Complex.regularizedGaussHGFunSeries a b c).derivSeries
  have hz' : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have hsum₀ : HasSum (fun n : ℕ ↦ A n * z ^ n)
      (regularizedGaussHypergeometricSeriesSum a b c z) := by
    simpa [A, FormalMultilinearSeries.apply_eq_prod_smul_coeff, mul_comm] using
      (regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall a b c).hasSum hz'
  have hsum₁ : HasSum (fun n : ℕ ↦ (n + 1 : ℂ) * A (n + 1) * z ^ n)
      (deriv (regularizedGaussHypergeometricSeriesSum a b c) z) := by
    simpa [A, FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using
      (regularizedGauss_firstDerivative_hasFPowerSeriesOnBall a b c).hasSum hz'
  have hp₁ (n : ℕ) : p₁.coeff n = (n + 1 : ℂ) * A (n + 1) := by
    change ((Complex.regularizedGaussHGFunSeries a b c).derivSeries.coeff n) 1 = _
    simp only [FormalMultilinearSeries.derivSeries_coeff_one,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, A]
  have hp₂ (n : ℕ) :
      ((ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries
        (((ContinuousLinearMap.apply ℂ ℂ 1).compFormalMultilinearSeries
          (Complex.regularizedGaussHGFunSeries a b c).derivSeries).derivSeries)).coeff n =
          (n + 1 : ℂ) * ((n + 2 : ℂ) * A (n + 2)) := by
    change (p₁.derivSeries.coeff n) 1 = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [nsmul_eq_mul, hp₁, Nat.cast_add, Nat.cast_one]
    rw [show n + 1 + 1 = n + 2 by omega]
    rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
  have hsum₂ : HasSum
      (fun n : ℕ ↦ z ^ n * ((n + 1 : ℂ) * ((n + 2 : ℂ) * A (n + 2))))
      (deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) := by
    have h := (regularizedGauss_secondDerivative_hasFPowerSeriesOnBall a b c).hasSum hz'
    simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul, hp₂,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_add] using h
  clear hz'
  have hsum_zd2 : HasSum
      (fun n : ℕ ↦ (n : ℂ) * (n + 1 : ℂ) * A (n + 1) * z ^ n)
      (z * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) := by
    rw [← hasSum_nat_add_iff' 1]
    have hn2 (n : ℕ) : n + 1 + 1 = n + 2 := by omega
    have hcast2 (n : ℕ) : (n : ℂ) + 1 + 1 = (n : ℂ) + 2 := by ring
    simpa [Finset.sum_range_one, pow_succ, hn2, hcast2, Nat.cast_add, Nat.cast_one,
      mul_assoc, mul_comm, mul_left_comm] using hsum₂.mul_left z
  have hsum_z2d2 : HasSum
      (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) - 1) * A n * z ^ n)
      (z ^ 2 * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) := by
    rw [← hasSum_nat_add_iff' 2]
    have hterm (n : ℕ) :
        z ^ 2 * (z ^ n * ((n + 1 : ℂ) * ((n + 2 : ℂ) * A (n + 2)))) =
          ((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) - 1) * A (n + 2) *
            z ^ (n + 2) := by
      rw [Nat.cast_add, Nat.cast_ofNat,
        show (n : ℂ) + 2 - 1 = (n : ℂ) + 1 by ring, pow_add]
      norm_num [pow_two]
      ac_rfl
    have htail : HasSum
        (fun n : ℕ ↦ ((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) - 1) *
          A (n + 2) * z ^ (n + 2))
        (z ^ 2 * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) := by
      have hmul : HasSum
          (fun n : ℕ ↦ z ^ 2 * (z ^ n * ((n + 1 : ℂ) * ((n + 2 : ℂ) * A (n + 2)))))
          (z ^ 2 * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) := by
        simpa only using! hsum₂.mul_left (z ^ 2)
      convert hmul using 1
      funext n
      exact (hterm n).symm
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_mul, one_mul, sub_self, mul_zero, add_zero, sub_zero] using htail
  have hsum_zd1 : HasSum (fun n : ℕ ↦ (n : ℂ) * A n * z ^ n)
      (z * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one, pow_succ, Nat.cast_add, Nat.cast_one,
      mul_assoc, mul_comm, mul_left_comm] using hsum₁.mul_left z
  have hsum_cd1 : HasSum
      (fun n : ℕ ↦ c * ((n + 1 : ℂ) * A (n + 1) * z ^ n))
      (c * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) := by
    simpa only using! hsum₁.mul_left c
  have hsum_abzd1 : HasSum
      (fun n : ℕ ↦ (a + b + 1) * ((n : ℂ) * A n * z ^ n))
      ((a + b + 1) * (z * deriv (regularizedGaussHypergeometricSeriesSum a b c) z)) := by
    simpa only using! hsum_zd1.mul_left (a + b + 1)
  have hsum_aby : HasSum (fun n : ℕ ↦ (a * b) * (A n * z ^ n))
      ((a * b) * regularizedGaussHypergeometricSeriesSum a b c z) := by
    simpa only using! hsum₀.mul_left (a * b)
  let B : ℕ → ℂ := fun n ↦
    ((n : ℂ) * (n + 1 : ℂ) * A (n + 1) * z ^ n -
        (n : ℂ) * ((n : ℂ) - 1) * A n * z ^ n +
      c * ((n + 1 : ℂ) * A (n + 1) * z ^ n)) -
    (a + b + 1) * ((n : ℂ) * A n * z ^ n) -
    (a * b) * (A n * z ^ n)
  have hsum_B : HasSum B
      (((z * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z -
          z ^ 2 * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) +
        c * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) -
      (a + b + 1) * (z * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) -
      (a * b) * regularizedGaussHypergeometricSeriesSum a b c z) := by
    exact (((hsum_zd2.sub hsum_z2d2).add hsum_cd1).sub hsum_abzd1).sub hsum_aby
  have hB (n : ℕ) : B n = 0 := by
    have hrec : (n + 1 : ℂ) * (c + n) * A (n + 1) =
        (a + n) * (b + n) * A n := by
      simpa only [A] using regularizedGauss_coeff_recurrence a b c n
    dsimp only [B]
    calc
      _ = (((n + 1 : ℂ) * (c + n) * A (n + 1) -
          (a + n) * (b + n) * A n) * z ^ n) := by ring
      _ = 0 := by rw [hrec, sub_self, zero_mul]
  have hsum_B_zero : HasSum B 0 := by
    rw [show B = fun _ : ℕ ↦ (0 : ℂ) by funext n; exact hB n]
    exact hasSum_zero
  have hres := hsum_B.unique hsum_B_zero
  calc
    _ = (((z * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z -
          z ^ 2 * deriv (deriv (regularizedGaussHypergeometricSeriesSum a b c)) z) +
        c * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) -
      (a + b + 1) * (z * deriv (regularizedGaussHypergeometricSeriesSum a b c) z) -
      (a * b) * regularizedGaussHypergeometricSeriesSum a b c z) := by ring
    _ = 0 := hres

/-- For a source-valid denominator parameter, the ordinary local Gauss series satisfies the
unnormalized Gauss equation throughout the open unit disk.-/
theorem gaussHypergeometricSeriesSum_gaussEquation
    {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (deriv (gaussHypergeometricSeriesSum a b c)) z
      + (c - (a + b + 1) * z) * deriv (gaussHypergeometricSeriesSum a b c) z
      - a * b * gaussHypergeometricSeriesSum a b c z = 0 := by
  let O := gaussHypergeometricSeriesSum a b c
  let R := regularizedGaussHypergeometricSeriesSum a b c
  let G := Complex.Gamma c
  let U : Set ℂ := Metric.ball 0 1
  have hG : G ≠ 0 := Complex.Gamma_ne_zero hc
  have hOR : Set.EqOn O (fun w ↦ G * R w) U := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [U] using hw
    have hbridge := gaussHypergeometricSeriesSum_div_Gamma
      (a := a) (b := b) (c := c) (z := w) hc hw'
    have hmul : O w = R w * G := (div_eq_iff hG).mp hbridge
    simpa only [mul_comm] using hmul
  have hOR' : Set.EqOn (deriv O) (fun w ↦ G * deriv R w) U := by
    intro w hw
    simpa only [deriv_const_mul_field G] using (hOR.deriv Metric.isOpen_ball) hw
  have hOR'' : Set.EqOn (deriv (deriv O)) (fun w ↦ G * deriv (deriv R) w) U := by
    intro w hw
    simpa only [deriv_const_mul_field G] using (hOR'.deriv Metric.isOpen_ball) hw
  have hzU : z ∈ U := by simpa [U] using hz
  have h₀ := hOR hzU
  have h₁ := hOR' hzU
  have h₂ := hOR'' hzU
  have hR := regularizedGaussHypergeometricSeriesSum_gaussEquation
    (a := a) (b := b) (c := c) (z := z) hz
  change z * (1 - z) * deriv (deriv O) z + (c - (a + b + 1) * z) * deriv O z -
    a * b * O z = 0
  calc
    _ = G * (z * (1 - z) * deriv (deriv R) z +
        (c - (a + b + 1) * z) * deriv R z - a * b * R z) := by
      rw [h₀, h₁, h₂]
      ring
    _ = 0 := by rw [hR, mul_zero]

end LMLF.ODE
