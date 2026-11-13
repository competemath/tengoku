import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Nlalib.NLAlib.Matrix.Functions.CFCQuadratic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# The spectral measure of a symmetric matrix and a vector

For a real symmetric (Hermitian) matrix `A` with eigenpairs `(λᵢ, uᵢ)` (Mathlib's
`hA.eigenvalues`, `hA.eigenvectorBasis`) and a vector `v`, the spectral measure is the finite
atomic measure `μ_v = ∑ᵢ (uᵢ ⬝ v)² δ_{λᵢ}` on `ℝ`. Its defining property is
`∫ f dμ_v = vᵀ f(A) v` for every `f : ℝ → ℝ`, where `f(A) = cfc f A` is Mathlib's continuous
functional calculus (every function is continuous on the finite spectrum).

## Main results

* `NLAlib.spectralMeasure`, `NLAlib.integral_spectralMeasure`: `∫ f dμ_v = vᵀ f(A) v`.
* `NLAlib.integral_eval_spectralMeasure`, `NLAlib.integral_pow_spectralMeasure`:
  polynomial and moment forms, `∫ p dμ_v = vᵀ p(A) v`, `∫ xᵏ dμ_v = vᵀ Aᵏ v`;
  `NLAlib.integral_eval_mul_eval_spectralMeasure`: `∫ p p' dμ_v = (p(A) v) ⬝ (p'(A) v)`.
* `NLAlib.spectralMeasure_univ`: total mass `‖v‖²`;
  `NLAlib.spectralMeasure_compl_range_eigenvalues`:
  the measure lives on the eigenvalues.

The eigen-expansion `vᵀ f(A) v = ∑ᵢ f(λᵢ) (uᵢ ⬝ v)²` behind it is
`NLAlib.dotProduct_cfc_mulVec_eq_sum` (`NLAlib.Matrix.Functions.CFCQuadratic`).

The Hutchinson clause `𝔼_g[gᵀ f(A) g] = tr f(A)` of the atlas entry is `hutchinson-unbiased`
applied to `f(A)` and lives in `NLAlib.Estimation.Trace.Unbiased` (layer 4).

Source: Golub–Meurant (2010) [`gm10`], Ch. 7 (Riemann–Stieltjes integral form of `uᵀ f(A) u`);
Ubaru–Chen–Saad (2017) [`ucs17`], §2. Atlas: `spectral-measure`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral measure `μ_v = ∑ᵢ (uᵢ ⬝ v)² δ_{λᵢ}` of a symmetric matrix `A` and a vector `v`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7 (the measure `α(λ)` of the Riemann–Stieltjes
integral); Ubaru–Chen–Saad (2017) [`ucs17`], §2. Atlas: `spectral-measure`.
Deviation: indexed by Mathlib's eigenvalue enumeration, so repeated eigenvalues give repeated
atoms (the measure is the same).
atlas: spectral-measure-/
def spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) ^ 2) •
    Measure.dirac (hA.eigenvalues i)

/-- The spectral measure has total mass `‖v‖² = v ⬝ v`. Source: [`gm10`], Ch. 7.
Atlas: `spectral-measure`.
@isnad1 id=eq.1h3v.s6.f3989112dfb2 from=translated src=- shape=a4c31bab vocab=d1388009
-/
theorem spectralMeasure_univ {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    spectralMeasure hA v Set.univ = ENNReal.ofReal (v ⬝ᵥ v) := by
  rw [← sum_sq_eigenvectorBasis_dotProduct hA v, spectralMeasure,
    ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  simp

/-- The spectral measure is finite. Atlas: `spectral-measure`.
@isnad1 id=isfinite.1h3v.s5.7aa3a22fa713 from=translated src=- shape=90836065 vocab=cdeaa000
-/
instance isFiniteMeasure_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    IsFiniteMeasure (spectralMeasure hA v) :=
  ⟨by rw [spectralMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- The spectral measure is carried by the eigenvalues: the complement of
`Set.range hA.eigenvalues` is null. Source: [`gm10`], Ch. 7. Atlas: `spectral-measure`.
@isnad1 id=eq.1h3v.s6.ba47bfb1fe48 from=translated src=- shape=475eebba vocab=ec703f20
-/
theorem spectralMeasure_compl_range_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) : spectralMeasure hA v (Set.range hA.eigenvalues)ᶜ = 0 := by
  simp only [spectralMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply, Set.indicator_of_notMem (by simp), mul_zero]

/-- **Defining property of the spectral measure**: for symmetric `A`, any `v` and any
`f : ℝ → ℝ`, `∫ f dμ_v = vᵀ f(A) v` with `f(A) = cfc f A`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7, eq. (7.1)–(7.2); Ubaru–Chen–Saad (2017)
[`ucs17`], eq. (2). Atlas: `spectral-measure`.
Deviation: no continuity or measurability of `f` needed (the measure is atomic).
atlas: spectral-measure
@isnad1 id=eq.1h4v.s7.1f9e772abe3b from=translated src=- shape=fb37472b vocab=565a09fe
-/
theorem integral_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (f : ℝ → ℝ) : ∫ x, f x ∂spectralMeasure hA v = v ⬝ᵥ (cfc f A *ᵥ v) := by
  rw [dotProduct_cfc_mulVec_eq_sum hA f v, spectralMeasure,
    integral_finsetSum_measure fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    mul_comm]

/-- Polynomial form: `∫ p dμ_v = vᵀ p(A) v` for every real polynomial `p`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7. Atlas: `spectral-measure`.
atlas: spectral-measure
@isnad1 id=eq.1h4v.s7.a84c84f90a4b from=translated src=- shape=0133f47e vocab=787d37e8
-/
theorem integral_eval_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂spectralMeasure hA v = v ⬝ᵥ (Polynomial.aeval A p *ᵥ v) := by
  rw [integral_spectralMeasure hA v, cfc_polynomial p A hA.isSelfAdjoint]

/-- Moment form: `∫ xᵏ dμ_v = vᵀ Aᵏ v`. Source: Golub–Meurant (2010) [`gm10`], Ch. 7
(the moments of the spectral measure). Atlas: `spectral-measure`.
atlas: spectral-measure
@isnad1 id=eq.1h4v.s7.1672621e04f1 from=translated src=- shape=8211ef90 vocab=d83314e7
-/
theorem integral_pow_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (k : ℕ) : ∫ x, x ^ k ∂spectralMeasure hA v = v ⬝ᵥ ((A ^ k) *ᵥ v) := by
  simpa using integral_eval_spectralMeasure hA v (Polynomial.X ^ k)

open Polynomial in
/-- For symmetric `A`, `∫ p p' dμ_b = (p(A) b) ⬝ (p'(A) b)`. Helper for `spectral-measure`.
@isnad1 id=eq.1h5v.s8.ac038429f052 from=translated src=- shape=c13ff316 vocab=361b36ad
-/
theorem integral_eval_mul_eval_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) (p p' : ℝ[X]) :
    ∫ x, p.eval x * p'.eval x ∂spectralMeasure hA b = (aeval A p *ᵥ b) ⬝ᵥ (aeval A p' *ᵥ b) := by
  have h := integral_eval_spectralMeasure hA b (p * p')
  simp only [eval_mul] at h
  rw [h, map_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    transpose_aeval hA]

/-- Quadratic-form spelling: `∫ f dμ_v = quadForm (f(A)) v`. Atlas: `spectral-measure`.
@isnad1 id=eq.1h4v.s7.321bc2fd60d3 from=translated src=- shape=05d1448f vocab=3981ad50
-/
theorem integral_spectralMeasure_eq_quadForm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) (f : ℝ → ℝ) : ∫ x, f x ∂spectralMeasure hA v = quadForm (cfc f A) v :=
  integral_spectralMeasure hA v f

end NLAlib
