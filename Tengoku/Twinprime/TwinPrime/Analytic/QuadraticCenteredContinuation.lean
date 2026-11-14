import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticCenteredCoefficients
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticCenteredFunction
import Tengoku.Twinprime.TwinPrime.Analytic.PowerDirichletContinuation
import Tengoku.Seed.NumberTheory.LSeries.Linearity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered continuation after subtracting the quadratic-product residue

The centered coefficients have an actual nine-tenths-power prefix bound.
Their ordered Dirichlet series represents the entire pole-canceled product,
as follows from absolute convergence to the right of one and analytic
uniqueness. Its quantitative tail remains valid below one.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/--
@isnad1 id=lseriess.1h4v.s5.f8535710b0bc from=translated src=- shape=3ef11502 vocab=11976317
-/
theorem LSeriesSummable_centeredQuadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (centeredQuadraticProductCoefficients χ₁ χ₂) s := by
  change LSeriesSummable ((quadraticProductCoefficients χ₁ χ₂ : ℕ → ℂ) -
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 •
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ)) s
  exact (LSeriesSummable_quadraticProductCoefficients χ₁ χ₂ hs).sub
    (LSeriesSummable.smul _ (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs))

/--
@isnad1 id=eq.1h4v.s6.aa0ec9ff3683 from=translated src=- shape=f7188a91 vocab=243211e6
-/
theorem LSeries_centeredQuadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (centeredQuadraticProductCoefficients χ₁ χ₂) s =
      centeredQuadraticLFunctionProduct χ₁ χ₂ s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [centeredQuadraticLFunctionProduct_eq_of_ne_one χ₁ χ₂ s hs1]
  change LSeries ((quadraticProductCoefficients χ₁ χ₂ : ℕ → ℂ) -
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 •
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ)) s = _
  have hz : LSeriesSummable ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hzEq : LSeries ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) s =
      riemannZeta s := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [LSeries_sub (LSeriesSummable_quadraticProductCoefficients χ₁ χ₂ hs)
    (LSeriesSummable.smul (regularizedQuadraticLFunctionProduct χ₁ χ₂ 1) hz),
    LSeries_smul, LSeries_quadraticProductCoefficients χ₁ χ₂ hs,
    hzEq]
  rfl

/-- No convergence or residue hypothesis is assumed on the enlarged half-plane.
@isnad1 id=eqon.3h3v.s8.53cc27c26c82 from=translated src=- shape=411f1e4a vocab=504960c2
-/
theorem powerDirichletLimit_centeredQuadraticProductCoefficients_eqOn
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    Set.EqOn (powerDirichletLimit (centeredQuadraticProductCoefficients χ₁ χ₂))
      (centeredQuadraticLFunctionProduct χ₁ χ₂) {s : ℂ | (9 / 10 : ℝ) < s.re} := by
  apply powerDirichletLimit_eqOn_of_LSeries_right (9 / 10) (by norm_num) _
    (441 * (1 + 3250 * (q : ℝ) ^ 2)) (by positivity)
    (norm_centeredQuadraticProductCoefficients_prefix_le χ₁ χ₂ hχ₁ hχ₂ hχ₁₂) _
    (differentiable_centeredQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂ hχ₁₂).differentiableOn
  · intro s hs
    exact LSeriesSummable_centeredQuadraticProductCoefficients χ₁ χ₂
      ((le_max_right (9 / 10 : ℝ) 1).trans_lt hs)
  · intro s hs
    exact LSeries_centeredQuadraticProductCoefficients χ₁ χ₂
      ((le_max_right (9 / 10 : ℝ) 1).trans_lt hs)

/--
@isnad1 id=tendsto.4h4v.s8.4c9425a90afd from=translated src=- shape=7e6477a1 vocab=85551082
-/
theorem tendsto_centeredQuadraticProduct_partialSum
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (s : ℂ) (hs : (9 / 10 : ℝ) < s.re) :
    Tendsto (powerDirichletPartialSum (centeredQuadraticProductCoefficients χ₁ χ₂) s)
      atTop (𝓝 (centeredQuadraticLFunctionProduct χ₁ χ₂ s)) := by
  rw [← powerDirichletLimit_centeredQuadraticProductCoefficients_eqOn χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hs]
  exact tendsto_powerDirichletPartialSum_limit (9 / 10) (by norm_num) _
    (441 * (1 + 3250 * (q : ℝ) ^ 2)) (by positivity)
    (norm_centeredQuadraticProductCoefficients_prefix_le χ₁ χ₂ hχ₁ hχ₂ hχ₁₂) s hs

/--
@isnad1 id=le.5h5v.s9.f87975a78a78 from=translated src=- shape=5767e036 vocab=524e2218
-/
theorem norm_centeredQuadraticLFunctionProduct_sub_partialSum_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : (9 / 10 : ℝ) < s.re) :
    ‖centeredQuadraticLFunctionProduct χ₁ χ₂ s -
      powerDirichletPartialSum (centeredQuadraticProductCoefficients χ₁ χ₂) s M‖ ≤
      (882 * (1 + 3250 * (q : ℝ) ^ 2)) * (M : ℝ) ^ ((9 / 10 : ℝ) - s.re) *
        (1 + ‖s‖ / (s.re - (9 / 10 : ℝ))) := by
  have h := norm_sub_powerDirichletPartialSum_le_of_eqOn (9 / 10) (by norm_num) _
    (441 * (1 + 3250 * (q : ℝ) ^ 2)) (by positivity)
    (norm_centeredQuadraticProductCoefficients_prefix_le χ₁ χ₂ hχ₁ hχ₂ hχ₁₂) _
    (powerDirichletLimit_centeredQuadraticProductCoefficients_eqOn χ₁ χ₂ hχ₁ hχ₂ hχ₁₂)
    M hM s hs
  convert h using 1
  ring

/-- A uniform tail bound in a fixed real interval immediately below one.
@isnad1 id=le.6h5v.s8.7a67ae68f388 from=translated src=- shape=c025adbe vocab=20065966
-/
theorem norm_centeredQuadraticLFunctionProduct_real_sub_partialSum_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β ≤ 1) :
    ‖centeredQuadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
      powerDirichletPartialSum (centeredQuadraticProductCoefficients χ₁ χ₂) (β : ℂ) M‖ ≤
      18522 * (1 + 3250 * (q : ℝ) ^ 2) * (M : ℝ) ^ (-(1 / 20 : ℝ)) := by
  have hσ : (9 / 10 : ℝ) + 1 / 20 ≤ (β : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hnorm : ‖(β : ℂ)‖ ≤ (1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ β)]
    exact hβ1
  have h := norm_powerDirichletLimit_sub_partialSum_le_uniform (9 / 10) (by norm_num) _
    (441 * (1 + 3250 * (q : ℝ) ^ 2)) (by positivity)
    (norm_centeredQuadraticProductCoefficients_prefix_le χ₁ χ₂ hχ₁ hχ₂ hχ₁₂)
    M hM (1 / 20) 1 (by norm_num) (β : ℂ) hσ hnorm
  rw [powerDirichletLimit_centeredQuadraticProductCoefficients_eqOn χ₁ χ₂ hχ₁ hχ₂ hχ₁₂
    (by change (9 / 10 : ℝ) < β; linarith)] at h
  convert h using 1
  norm_num
  ring

end TwinPrime.Analytic
