/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.Interlacing
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.LaguerrePolyaApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jensen polynomials and the Jensen--Pólya approximation interface

For a real sequence `γ`, the shifted Jensen polynomial is

`Jᵈ,ⁿ_γ(X) = ∑_{k=0}^d choose(d,k) γ(n+k) X^k`.

The file defines hyperbolicity literally as nonzeroness plus real location of
every complex root.  It also isolates the exact analytic input in Jensen's
approximation theorem: locally uniform convergence of the rescaled
polynomials `J^(d+1),0_γ (X/(d+1))`.

Mathlib v4.31 has polynomial roots and locally uniform convergence, but no
native Jensen-polynomial, hyperbolicity, multiplier-sequence, or
Laguerre--Pólya API.  Consequently the convergence statement is represented
by `JensenConvergenceData`; no classical implication is inserted as an axiom.
Once convergence and hyperbolicity are supplied, the conversion to the
project's `LaguerrePolyaApproximationData` is proved here.
-/

namespace OverflowResidueRH

open Complex Filter Set Topology

/-- The shifted Jensen polynomial over its natural coefficient field `ℝ`.-/
noncomputable def realJensenPolynomial
    (γ : ℕ → ℝ) (n d : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C ((Nat.choose d k : ℝ) * γ (n + k)) *
      Polynomial.X ^ k

/-- The shifted degree-`d` Jensen polynomial of a real sequence, viewed over
`ℂ` so that zero location can be stated without an additional scalar map.-/
noncomputable def jensenPolynomial
    (γ : ℕ → ℝ) (n d : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (((Nat.choose d k : ℝ) * γ (n + k) : ℝ) : ℂ) *
      Polynomial.X ^ k

/-! ## Exact finite-polynomial identities -/

/-- Exact coefficient formula for a Jensen polynomial.-/
theorem jensenPolynomial_coeff
    (γ : ℕ → ℝ) (n d k : ℕ) :
    (jensenPolynomial γ n d).coeff k =
      if k ≤ d then (((Nat.choose d k : ℝ) * γ (n + k) : ℝ) : ℂ)
      else 0 := by
  classical
  simp only [jensenPolynomial]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ≤ d
  · rw [ite_eq_left hk]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Ne.symm hbk]
    · simp [Nat.lt_succ_iff.mpr hk]
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : b ≠ k := by
      intro h
      subst b
      exact hk (Nat.le_of_lt_succ (Finset.mem_range.mp hb))
    simp [Ne.symm hbk]

/-- Exact Jensen differentiation identity
`(J_γ^{d+1,n})' = (d+1) J_γ^{d,n+1}`.  This is the finite algebraic
mechanism behind passage from unshifted to shifted Jensen polynomials.-/
theorem jensenPolynomial_derivative_succ
    (γ : ℕ → ℝ) (n d : ℕ) :
    (jensenPolynomial γ n (d + 1)).derivative =
      Polynomial.C ((d + 1 : ℕ) : ℂ) * jensenPolynomial γ (n + 1) d := by
  ext k
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
    jensenPolynomial_coeff, jensenPolynomial_coeff]
  by_cases hk : k ≤ d
  · rw [ite_eq_left hk, ite_eq_left (Nat.succ_le_succ hk)]
    push_cast
    have hchoose :
        (((d + 1).choose (k + 1) : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) =
          ((d + 1 : ℕ) : ℂ) * ((d.choose k : ℕ) : ℂ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
    rw [show n + (k + 1) = n + 1 + k by omega]
    calc
      (((d + 1).choose (k + 1) : ℕ) : ℂ) *
            ((γ (n + 1 + k) : ℝ) : ℂ) * ((k : ℂ) + 1) =
          ((((d + 1).choose (k + 1) : ℕ) : ℂ) *
            ((k + 1 : ℕ) : ℂ)) * ((γ (n + 1 + k) : ℝ) : ℂ) := by
              push_cast
              ring
      _ = (((d + 1 : ℕ) : ℂ) * ((d.choose k : ℕ) : ℂ)) *
            ((γ (n + 1 + k) : ℝ) : ℂ) := by rw [hchoose]
      _ = ((d : ℂ) + 1) *
            (((d.choose k : ℕ) : ℂ) * ((γ (n + 1 + k) : ℝ) : ℂ)) := by
              push_cast
              ring
  · rw [ite_eq_right hk]
    have hksucc : ¬ k + 1 ≤ d + 1 := by omega
    rw [ite_eq_right hksucc]
    simp

/-- Hyperbolicity in the literal zero-location sense used by this project.
The nonzero condition excludes the zero polynomial, whose every complex
number would otherwise be a root.-/
def PolynomialHyperbolic (p : Polynomial ℂ) : Prop :=
  p ≠ 0 ∧ ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0

namespace PolynomialHyperbolic

/-- Gauss--Lucas gives a fully formal finite-dimensional closure theorem:
the nonzero derivative of a hyperbolic polynomial is hyperbolic.-/
theorem derivative {p : Polynomial ℂ}
    (hp : PolynomialHyperbolic p) (hderiv : p.derivative ≠ 0) :
    PolynomialHyperbolic p.derivative := by
  constructor
  · exact hderiv
  · apply polynomial_derivative_roots_real
    · have hn : 0 < p.natDegree :=
        (Polynomial.derivative_ne_zero.mp hderiv).bot_lt
      exact Polynomial.natDegree_pos_iff_degree_pos.mp hn
    · exact hp.2

/-- Removing a constant polynomial factor preserves hyperbolicity whenever
the product itself is hyperbolic.-/
theorem of_C_mul {p : Polynomial ℂ} {c : ℂ}
    (h : PolynomialHyperbolic (Polynomial.C c * p)) :
    PolynomialHyperbolic p := by
  constructor
  · intro hpzero
    apply h.1
    simp [hpzero]
  · intro ρ hρ
    apply h.2 ρ
    simp [hρ]

end PolynomialHyperbolic

/-- Every shifted Jensen polynomial of `γ` is hyperbolic.-/
def JensenPolynomialHyperbolicity (γ : ℕ → ℝ) : Prop :=
  ∀ n d : ℕ, PolynomialHyperbolic (jensenPolynomial γ n d)

/-- Hyperbolicity of the unshifted Jensen polynomials.  This is the form
appearing in Jensen's approximation theorem for the exponential generating
function `∑ γ(k) z^k/k!`; all-shifts hyperbolicity is strictly stronger.-/
def JensenPolynomialHyperbolicityAtOrigin (γ : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, PolynomialHyperbolic (jensenPolynomial γ 0 d)

/-- All-shifts hyperbolicity implies the unshifted predicate.-/
theorem JensenPolynomialHyperbolicity.atOrigin
    {γ : ℕ → ℝ} (hγ : JensenPolynomialHyperbolicity γ) :
    JensenPolynomialHyperbolicityAtOrigin γ :=
  hγ 0

/-- One differentiation step converts hyperbolicity of `J^{d+1,n}` into
hyperbolicity of `J^{d,n+1}`, provided the latter polynomial is not the zero
polynomial.  The displayed coefficient condition is exactly what ensures
that nondegeneracy.-/
theorem jensenPolynomial_hyperbolic_shift_of_succ
    {γ : ℕ → ℝ} {n d : ℕ}
    (h : PolynomialHyperbolic (jensenPolynomial γ n (d + 1)))
    (hγ : γ (n + 1 + d) ≠ 0) :
    PolynomialHyperbolic (jensenPolynomial γ (n + 1) d) := by
  have hJne : jensenPolynomial γ (n + 1) d ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff d) hzero
    rw [jensenPolynomial_coeff, ite_eq_left le_rfl] at hcoeff
    simp [hγ] at hcoeff
  have hderiv_ne : (jensenPolynomial γ n (d + 1)).derivative ≠ 0 := by
    rw [jensenPolynomial_derivative_succ]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero d)) hJne
  have hderiv := h.derivative hderiv_ne
  rw [jensenPolynomial_derivative_succ] at hderiv
  exact hderiv.of_C_mul

/-- Under the explicit nonvanishing hypothesis on every coefficient,
hyperbolicity of all unshifted Jensen polynomials implies hyperbolicity of
all shifted Jensen polynomials.  The hypothesis is necessary: a sequence
supported only at index zero has hyperbolic unshifted polynomials but zero
shifted polynomials.-/
theorem JensenPolynomialHyperbolicityAtOrigin.allShifts_of_ne_zero
    {γ : ℕ → ℝ}
    (H : JensenPolynomialHyperbolicityAtOrigin γ)
    (hγ : ∀ n : ℕ, γ n ≠ 0) :
    JensenPolynomialHyperbolicity γ := by
  intro n
  induction n with
  | zero =>
      intro d
      exact H d
  | succ n ih =>
      intro d
      exact jensenPolynomial_hyperbolic_shift_of_succ
        (ih (d + 1)) (hγ (n + 1 + d))

/-- The standard Jensen rescaling `J^(d+1),0_γ (X/(d+1))`.  The `d+1`
index avoids division by zero and gives a sequence indexed by all naturals.-/
noncomputable def rescaledJensenPolynomial
    (γ : ℕ → ℝ) (d : ℕ) : Polynomial ℂ :=
  (jensenPolynomial γ 0 (d + 1)).comp
    (Polynomial.C (Complex.ofReal (((d + 1 : ℕ) : ℝ)⁻¹)) * Polynomial.X)

/-- Jensen polynomials have real coefficients, hence obey Schwarz
reflection after evaluation.-/
theorem jensenPolynomial_schwarz
    (γ : ℕ → ℝ) (n d : ℕ) (z : ℂ) :
    (jensenPolynomial γ n d).eval (star z) =
      star ((jensenPolynomial γ n d).eval z) := by
  simp only [jensenPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  change (∑ k ∈ Finset.range (d + 1),
      (((Nat.choose d k : ℝ) * γ (n + k) : ℝ) : ℂ) * (star z) ^ k) =
    (starRingEnd ℂ) (∑ k ∈ Finset.range (d + 1),
      (((Nat.choose d k : ℝ) * γ (n + k) : ℝ) : ℂ) * z ^ k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- The standard rescaling preserves the real-coefficient Schwarz
reflection identity.-/
theorem rescaledJensenPolynomial_schwarz
    (γ : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    (rescaledJensenPolynomial γ d).eval (star z) =
      star ((rescaledJensenPolynomial γ d).eval z) := by
  unfold rescaledJensenPolynomial
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  simpa [Complex.star_def, map_mul, Complex.conj_ofReal] using
    jensenPolynomial_schwarz γ 0 (d + 1)
      (Complex.ofReal (((d + 1 : ℕ) : ℝ)⁻¹) * z)

/-- The all-shifts hyperbolicity predicate supplies hyperbolicity of every
member of the standard rescaled approximation sequence.-/
theorem JensenPolynomialHyperbolicityAtOrigin.rescaled
    {γ : ℕ → ℝ} (hγ : JensenPolynomialHyperbolicityAtOrigin γ) (d : ℕ) :
    PolynomialHyperbolic (rescaledJensenPolynomial γ d) := by
  unfold rescaledJensenPolynomial
  let q := Polynomial.C (Complex.ofReal (((d + 1 : ℕ) : ℝ)⁻¹)) * Polynomial.X
  have hJ := hγ (d + 1)
  constructor
  · intro hzero
    rcases Polynomial.comp_eq_zero_iff.mp hzero with hJzero | hconstant
    · exact hJ.1 hJzero
    · have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) hconstant.2
      norm_num [q] at hcoeff
      have hsucc : (d : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero d
      exact hsucc hcoeff
  · intro ρ hρ
    have hroot :
        (jensenPolynomial γ 0 (d + 1)).eval
          (Complex.ofReal (((d + 1 : ℕ) : ℝ)⁻¹) * ρ) = 0 := by
      simpa [Polynomial.eval_comp] using hρ
    have him := hJ.2 _ hroot
    have him' : ((d + 1 : ℕ) : ℝ)⁻¹ * ρ.im = 0 := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] at him
      exact him
    have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ)⁻¹ := by positivity
    exact (mul_eq_zero.mp him').resolve_left (ne_of_gt hpos)

/-- The missing analytic half of the classical Jensen approximation theorem:
the standard rescaled polynomials converge locally uniformly to `F`.

This is data rather than a theorem because pinned Mathlib has no theorem
connecting an exponential generating series to rescaled Jensen polynomials.-/
structure JensenConvergenceData (F : ℂ → ℂ) (γ : ℕ → ℝ) : Prop where
  tendstoLocallyUniformly :
    TendstoLocallyUniformlyOn
      (fun d z => (rescaledJensenPolynomial γ d).eval z)
      F atTop Set.univ

/-- Hyperbolicity plus the exact Jensen convergence input gives a genuine
Laguerre--Pólya approximation in the function-level sense already used by
the repository.-/
noncomputable def JensenConvergenceData.toLaguerrePolyaApproximationData
    {F : ℂ → ℂ} {γ : ℕ → ℝ}
    (C : JensenConvergenceData F γ)
    (H : JensenPolynomialHyperbolicityAtOrigin γ) :
    LaguerrePolyaApproximationData F where
  approximant := rescaledJensenPolynomial γ
  approximant_ne_zero := fun d => (H.rescaled d).1
  approximant_roots_real := fun d => (H.rescaled d).2
  approximant_schwarz := rescaledJensenPolynomial_schwarz γ
  tendstoLocallyUniformly := C.tendstoLocallyUniformly

/-- A nontrivial Jensen limit has only real zeros once the explicit
hyperbolicity and convergence inputs are supplied.-/
theorem roots_real_of_jensen_hyperbolicity
    {F : ℂ → ℂ} {γ : ℕ → ℝ}
    (C : JensenConvergenceData F γ)
    (H : JensenPolynomialHyperbolicityAtOrigin γ)
    (h_nontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  (C.toLaguerrePolyaApproximationData H).roots_real h_nontrivial

end OverflowResidueRH
