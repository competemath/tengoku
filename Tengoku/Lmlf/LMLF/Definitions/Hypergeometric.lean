import Tengoku.Seed.Analysis.Analytic.ChangeOrigin
import Tengoku.Seed.Analysis.SpecialFunctions.RegularizedHypergeometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/LMLF@00f4ab46c750, `LMLF/Definitions/Hypergeometric.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Local Gauss hypergeometric series

This file exposes the ordinary and regularized Gauss hypergeometric series as ambient complex
functions on their source domain, the open unit disk.  It deliberately does not define an analytic
continuation or a principal branch.
-/

namespace LMLF.Definitions

/-- The ordinary Gauss hypergeometric local-series sum.

This is a transparent view of Mathlib's `.sum`, a totalized `tsum`.  In particular, its value at a
point where no convergence theorem applies is not an analytically continued value.-/
noncomputable def gaussHypergeometricSeriesSum (a b c : ℂ) : ℂ → ℂ :=
  ordinaryHypergeometric a b c

/-- The regularized Gauss hypergeometric local-series sum.

This is a transparent view of Mathlib's `.sum`, a totalized `tsum`.  In particular, its value at a
point where no convergence theorem applies is not an analytically continued value.-/
noncomputable def regularizedGaussHypergeometricSeriesSum (a b c : ℂ) : ℂ → ℂ :=
  Complex.regularizedGaussHGFun a b c

/-- For a source-valid denominator parameter, the ordinary Gauss series has radius at least one.
@isnad1 id=le.1h3v.s6.84aa18accb1b from=translated src=- shape=13beb4ee vocab=69240c96
-/
theorem ordinaryHypergeometricSeries_radius_ge_one
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  rcases em (∃ n : ℕ, a = -(n : ℂ)) with ⟨n, rfl⟩ | ha
  · rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  rcases em (∃ n : ℕ, b = -(n : ℂ)) with ⟨n, rfl⟩ | hb
  · rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact le_top
  have habc : ∀ n : ℕ,
      (n : ℂ) ≠ -a ∧ (n : ℂ) ≠ -b ∧ (n : ℂ) ≠ -c := by
    intro n
    refine ⟨?_, ?_, ?_⟩
    · intro h
      apply ha
      exact ⟨n, by simpa using congrArg Neg.neg h.symm⟩
    · intro h
      apply hb
      exact ⟨n, by simpa using congrArg Neg.neg h.symm⟩
    · intro h
      exact hc n (by simpa using congrArg Neg.neg h.symm)
  rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c habc]

/-- The ordinary Gauss sum has its defining power series throughout the open unit disk.
@isnad1 id=hasfpowe.1h3v.s6.ebe7181578c1 from=translated src=- shape=15e718fc vocab=f59e56e1
-/
theorem gaussHypergeometricSeriesSum_hasFPowerSeriesOnBall
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasFPowerSeriesOnBall
      (gaussHypergeometricSeriesSum a b c)
      (ordinaryHypergeometricSeries ℂ a b c) 0 1 := by
  have hr := ordinaryHypergeometricSeries_radius_ge_one (a := a) (b := b) (c := c) hc
  have hr_pos : 0 < (ordinaryHypergeometricSeries ℂ a b c).radius :=
    lt_of_lt_of_le zero_lt_one hr
  change HasFPowerSeriesOnBall (fun z ↦
    (ordinaryHypergeometricSeries ℂ a b c).sum z) (ordinaryHypergeometricSeries ℂ a b c) 0 1
  exact ((ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall hr_pos).mono
    zero_lt_one hr

/-- The regularized Gauss sum has its defining power series throughout the open unit disk.
@isnad1 id=hasfpowe.0h3v.s5.5d9a8791fae1 from=translated src=- shape=9f25ffc5 vocab=c39aba50
-/
theorem regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall (a b c : ℂ) :
    HasFPowerSeriesOnBall
      (regularizedGaussHypergeometricSeriesSum a b c)
      (Complex.regularizedGaussHGFunSeries a b c) 0 1 := by
  have hr := Complex.radius_regularizedGaussHGFunSeries_ge_one a b c
  have hr_pos : 0 < (Complex.regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le zero_lt_one hr
  change HasFPowerSeriesOnBall (fun z ↦
    (Complex.regularizedGaussHGFunSeries a b c).sum z)
    (Complex.regularizedGaussHGFunSeries a b c) 0 1
  exact ((Complex.regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hr_pos).mono
    zero_lt_one hr

/-- The ordinary Gauss coefficients genuinely sum to the named local series inside the unit disk.
@isnad1 id=hassum.2h4v.s7.03a71f739e82 from=translated src=- shape=885cac1c vocab=07a315c6
-/
theorem hasSum_gaussHypergeometricSeries
    {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ ↦
        ((Nat.factorial n : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a *
          (ascPochhammer ℂ n).eval b * ((ascPochhammer ℂ n).eval c)⁻¹) * z ^ n)
      (gaussHypergeometricSeriesSum a b c z) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have h := (gaussHypergeometricSeriesSum_hasFPowerSeriesOnBall
    (a := a) (b := b) (c := c) hc).hasSum hz'
  simpa only [ordinaryHypergeometricSeries_apply_eq (𝔸 := ℂ), smul_eq_mul, zero_add] using h

/-- The regularized Gauss coefficients genuinely sum to the named local series inside the unit
disk.
@isnad1 id=hassum.1h4v.s7.8c57de474d4d from=translated src=- shape=2310ce15 vocab=d76db093
-/
theorem hasSum_regularizedGaussHypergeometricSeries
    {a b c z : ℂ} (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ ↦
        ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
          ((Nat.factorial n : ℂ) * Complex.Gamma (c + n))) * z ^ n)
      (regularizedGaussHypergeometricSeriesSum a b c z) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Complex.coeff_regularizedGaussHGFunSeries, mul_comm] using
    (regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall a b c).hasSum hz'

/-- On the source disk, the ordinary local series divided by `Gamma c` is the regularized series.
@isnad1 id=eq.2h4v.s5.b251ba36dd49 from=translated src=- shape=1c5ec7d9 vocab=022239cb
-/
theorem gaussHypergeometricSeriesSum_div_Gamma
    {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    gaussHypergeometricSeriesSum a b c z / Complex.Gamma c =
      regularizedGaussHypergeometricSeriesSum a b c z := by
  exact Complex.ordinaryHypergeometric_div_Gamma_eq hc

/-- The source-valid ordinary Gauss local series is normalized to one at the origin.
@isnad1 id=eq.1h3v.s5.b22d5a9553ec from=translated src=- shape=665a869b vocab=bceb7d46
-/
@[simp] theorem gaussHypergeometricSeriesSum_zero
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    gaussHypergeometricSeriesSum a b c 0 = 1 := by
  exact ordinaryHypergeometric_zero a b c

/-- The regularized Gauss local series has constant term `(Gamma c)⁻¹`.
@isnad1 id=eq.0h3v.s4.f5e0bd002b2d from=translated src=- shape=8431c51b vocab=b16ebcea
-/
@[simp] theorem regularizedGaussHypergeometricSeriesSum_zero (a b c : ℂ) :
    regularizedGaussHypergeometricSeriesSum a b c 0 = (Complex.Gamma c)⁻¹ := by
  have hcoeff :=
    (regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall a b c).coeff_zero
      (fun i : Fin 0 ↦ nomatch i)
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Complex.coeff_regularizedGaussHGFunSeries] at hcoeff
  simpa using hcoeff.symm

/-- The ordinary Gauss local-series sum is analytic throughout the open unit disk.
@isnad1 id=analytic.1h3v.s6.72195eab4eab from=translated src=- shape=3ca6980e vocab=e147a29d
-/
theorem gaussHypergeometricSeriesSum_analyticOnNhd
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (gaussHypergeometricSeriesSum a b c) (Metric.ball 0 1) := by
  have h := (gaussHypergeometricSeriesSum_hasFPowerSeriesOnBall
    (a := a) (b := b) (c := c) hc).analyticOnNhd
  rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at h
  simpa using h

/-- The regularized Gauss local-series sum is analytic throughout the open unit disk.
@isnad1 id=analytic.0h3v.s5.0fef99bf0587 from=translated src=- shape=de6a368a vocab=e88c3884
-/
theorem regularizedGaussHypergeometricSeriesSum_analyticOnNhd (a b c : ℂ) :
    AnalyticOnNhd ℂ (regularizedGaussHypergeometricSeriesSum a b c) (Metric.ball 0 1) := by
  have h :=
    (regularizedGaussHypergeometricSeriesSum_hasFPowerSeriesOnBall a b c).analyticOnNhd
  rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at h
  simpa using h

end LMLF.Definitions
