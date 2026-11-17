/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.EntireFunctions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A first Laguerre--Pólya approximation layer

Pinned Mathlib has the Weierstrass theorem for locally uniform limits and
convergence of logarithmic derivatives, but no native Laguerre--Pólya,
Hermite--Biehler, de Branges, or polynomial-interlacing API.  This file builds
the first reusable layer needed here directly from those available pieces.

`LaguerrePolyaApproximationData F` records a locally uniformly convergent
sequence of nonzero, Schwarz-symmetric complex polynomials whose zeros are all
real.  For a nonzero limit `F`, we prove:

* `F` is entire;
* Schwarz symmetry passes to `F`;
* the anti-Herglotz logarithmic-derivative sign passes to `F` away from zeros;
* consequently every zero of `F` is real.

The last step uses the project's already-discharged analytic local
factorization/pole-probe theorem.  Thus no unformalized appeal to Hurwitz's
theorem is hidden in the definition or proof.
-/

namespace OverflowResidueRH

open Complex Filter Set Topology

/-- Function-level Laguerre--Pólya approximation data: locally uniform
approximation by nonzero Schwarz-symmetric polynomials with only real zeros.

This packages the approximation property rather than claiming one of the
many equivalent growth/product characterizations of the classical
Laguerre--Pólya class.-/
structure LaguerrePolyaApproximationData (F : ℂ → ℂ) where
  approximant : ℕ → Polynomial ℂ
  approximant_ne_zero : ∀ n : ℕ, approximant n ≠ 0
  approximant_roots_real :
    ∀ n : ℕ, ∀ ρ : ℂ, (approximant n).eval ρ = 0 → ρ.im = 0
  approximant_schwarz :
    ∀ n : ℕ, ∀ z : ℂ,
      (approximant n).eval (star z) = star ((approximant n).eval z)
  tendstoLocallyUniformly :
    TendstoLocallyUniformlyOn
      (fun n z => (approximant n).eval z) F atTop Set.univ

/-- A Laguerre--Pólya approximable limit is entire (complex
differentiable everywhere).
@isnad1 id=differen.0h2v.s6.7c7e77753c14 from=translated src=- shape=4abcf43f vocab=6e7d5b09
-/
theorem LaguerrePolyaApproximationData.differentiable
    {F : ℂ → ℂ} (A : LaguerrePolyaApproximationData F) :
    Differentiable ℂ F := by
  have hdiffOn : DifferentiableOn ℂ F Set.univ :=
    A.tendstoLocallyUniformly.differentiableOn
      (Eventually.of_forall fun n => (A.approximant n).differentiableOn)
      isOpen_univ
  simpa only [differentiableOn_univ] using hdiffOn

/-- Schwarz symmetry is closed under locally uniform (indeed pointwise)
limits.
@isnad1 id=eq.0h3v.s6.0d704193a045 from=translated src=- shape=009ab79b vocab=9443b96b
-/
theorem LaguerrePolyaApproximationData.schwarz
    {F : ℂ → ℂ} (A : LaguerrePolyaApproximationData F) (z : ℂ) :
    F (star z) = star (F z) := by
  have h_at_star :
      Tendsto (fun n => (A.approximant n).eval (star z)) atTop
        (𝓝 (F (star z))) :=
    A.tendstoLocallyUniformly.tendsto_at (Set.mem_univ (star z))
  have h_at_z :
      Tendsto (fun n => (A.approximant n).eval z) atTop (𝓝 (F z)) :=
    A.tendstoLocallyUniformly.tendsto_at (Set.mem_univ z)
  have h_conj :
      Tendsto (fun n => star ((A.approximant n).eval z)) atTop
        (𝓝 (star (F z))) :=
    (tendsto_star (F z)).comp h_at_z
  have h_at_star' :
      Tendsto (fun n => (A.approximant n).eval (star z)) atTop
        (𝓝 (star (F z))) := by
    apply h_conj.congr'
    exact Eventually.of_forall fun n => (A.approximant_schwarz n z).symm
  exact tendsto_nhds_unique h_at_star h_at_star'

/-- The anti-Herglotz logarithmic-derivative sign of the real-rooted
approximating polynomials passes to the locally uniform limit at every point
where the limit is nonzero.
@isnad1 id=le.2h3v.s5.cdd497be7ae5 from=translated src=- shape=b0a1bd4a vocab=7b19f644
-/
theorem LaguerrePolyaApproximationData.logDerivative_im_nonpos_away
    {F : ℂ → ℂ} (A : LaguerrePolyaApproximationData F) :
    ∀ z : ℂ, 0 < z.im → F z ≠ 0 →
      (logDerivativeResponse F z).im ≤ 0 := by
  intro z hz hFz
  have hpolyDiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ (fun w => (A.approximant n).eval w) Set.univ :=
    Eventually.of_forall fun n => (A.approximant n).differentiableOn
  have hlog := Complex.logDeriv_tendsto
    isOpen_univ (Set.mem_univ z) A.tendstoLocallyUniformly hpolyDiff hFz
  have him :
      Tendsto
        (fun n => (logDeriv (fun w => (A.approximant n).eval w) z).im)
        atTop (𝓝 ((logDeriv F z).im)) :=
    (Complex.continuous_im.tendsto _).comp hlog
  have hpolySign :
      ∀ n : ℕ,
        (logDeriv (fun w => (A.approximant n).eval w) z).im ≤ 0 := by
    intro n
    have hanti :
        AntiHerglotzUHP
          (polynomialLogDerivResponse (A.approximant n)) :=
      (polynomial_antiHerglotz_iff_roots_closedLower
        (A.approximant n) (A.approximant_ne_zero n)).mpr
          (fun ρ hroot => (A.approximant_roots_real n ρ hroot).le)
    simpa [logDeriv_apply, polynomialLogDerivResponse] using hanti z hz
  have hlimit : (logDeriv F z).im ≤ 0 :=
    le_of_tendsto him (Eventually.of_forall hpolySign)
  simpa [logDerivativeResponse, logDeriv_apply] using hlimit

/-- Totalized anti-Herglotz form of the preceding punctured-domain theorem.
At zeros, both logarithmic-derivative conventions evaluate to zero.
@isnad1 id=antiherg.0h2v.s3.e0e4481d0a92 from=translated src=- shape=aef97f5f vocab=2cf0b225
-/
theorem LaguerrePolyaApproximationData.antiHerglotz
    {F : ℂ → ℂ} (A : LaguerrePolyaApproximationData F) :
    AntiHerglotzUHP (logDerivativeResponse F) :=
  (antiHerglotz_iff_antiHerglotz_away_from_zeros F).2
    A.logDerivative_im_nonpos_away

/-- **Laguerre--Pólya closure theorem.** A nontrivial locally uniform limit
of nonzero Schwarz-symmetric real-rooted polynomials has only real zeros.
@isnad1 id=eq.2h3v.s5.e2aeb2e6f1dd from=translated src=- shape=91b43b54 vocab=3e066fae
-/
theorem LaguerrePolyaApproximationData.roots_real
    {F : ℂ → ℂ} (A : LaguerrePolyaApproximationData F)
    (h_nontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  entire_function_roots_real_of_analytic_nontrivial F
    (A.differentiable.differentiableOn.analyticOnNhd isOpen_univ)
    h_nontrivial A.logDerivative_im_nonpos_away A.schwarz

end OverflowResidueRH
