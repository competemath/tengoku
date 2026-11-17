/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.Star
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.DerivativeCompanionHermiteBiehler
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.Interlacing
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hermite--Biehler functions and the interlacing theorem interface

This file formalizes the full upper-half-plane Hermite--Biehler *predicate*

`|E#(z)| < |E(z)|`, where `E#(z) = conj (E (conj z))`,

and proves that, for a Schwarz-symmetric `F`, the derivative companion
`E = F + iF'` is Hermite--Biehler exactly when the repository's strict
logarithmic-derivative condition holds.

Mathlib v4.31 contains neither the classical Hermite--Biehler interlacing
theorem nor a polynomial interlacing API.  The deep normalized polynomial
theorem is therefore exposed as
`NormalizedPolynomialHermiteBiehlerTheoremData`: a proposition-valued
interface with both directions and every side condition visible.  No global
postulate and no unconditional interlacing conclusion is introduced.
-/

namespace OverflowResidueRH

open Complex
open scoped ComplexConjugate

/-- The Hermite--Biehler reflection `E#(z) = conj (E(conj z))`.-/
def hermiteBiehlerSharp (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (E (star z))

/-- The full strict Hermite--Biehler inequality on the open upper
half-plane.  Analyticity is intentionally separate, allowing the algebraic
predicate to be reused before analytic hypotheses are attached.-/
def HermiteBiehlerUHP (E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → ‖hermiteBiehlerSharp E z‖ < ‖E z‖

/-- The no-real-zero Hermite--Biehler predicate used by the strict classical
interlacing theorem.  The extra clause is essential: `|E#|<|E|` in the open
upper half-plane alone permits real zeros, which produce common or multiple
zeros in the real and imaginary components.-/
def HermiteBiehlerNoRealZeros (E : ℂ → ℂ) : Prop :=
  HermiteBiehlerUHP E ∧ ∀ x : ℝ, E (x : ℂ) ≠ 0

/-- Analytic Hermite--Biehler data: an entire function satisfying the strict
upper-half-plane norm inequality.-/
structure EntireHermiteBiehlerData (E : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ E
  hermiteBiehler : HermiteBiehlerUHP E

/--
@isnad1 id=eq.0h2v.s3.ddd2480a98ba from=translated src=- shape=21082139 vocab=dd51a29d
-/
@[simp]
theorem hermiteBiehlerSharp_sharp (E : ℂ → ℂ) (z : ℂ) :
    hermiteBiehlerSharp (hermiteBiehlerSharp E) z = E z := by
  simp [hermiteBiehlerSharp]

/--
@isnad1 id=eq.0h3v.s5.c169e8604d31 from=translated src=- shape=9bf0e71e vocab=53a7e07f
-/
@[simp]
theorem hermiteBiehlerSharp_add (E G : ℂ → ℂ) (z : ℂ) :
    hermiteBiehlerSharp (fun w => E w + G w) z =
      hermiteBiehlerSharp E z + hermiteBiehlerSharp G z := by
  simp [hermiteBiehlerSharp]

/-- The derivative companion regarded as a single Hermite--Biehler
candidate.-/
noncomputable def derivativeCompanionEntireFunction
    (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z + Complex.I * deriv F z

/-- Differentiating a Schwarz-symmetric function preserves the reflected
derivative identity.  This uses Mathlib's `deriv_conj_conj`, including its
totalized behavior at nondifferentiability points.
@isnad1 id=eq.1h2v.s7.1ca802906e91 from=translated src=- shape=a714198f vocab=f678e65a
-/
theorem deriv_schwarz
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, F (star z) = star (F z)) (z : ℂ) :
    star (deriv F (star z)) = deriv F z := by
  have hfun : conj ∘ F ∘ conj = F := by
    funext w
    change star (F (star w)) = F w
    rw [hF]
    simp
  have hderiv := congrArg (fun f : ℂ → ℂ => deriv f z) hfun
  rw [deriv_conj_conj] at hderiv
  simpa [Function.comp_apply] using hderiv

/-- For Schwarz-symmetric `F`, the sharp reflection of `F + iF'` is exactly
`F - iF'`.
@isnad1 id=eq.1h2v.s7.7b9438f2fa0f from=translated src=- shape=7b097d46 vocab=b8bf4d75
-/
theorem hermiteBiehlerSharp_derivativeCompanionEntireFunction
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, F (star z) = star (F z)) (z : ℂ) :
    hermiteBiehlerSharp (derivativeCompanionEntireFunction F) z =
      F z - Complex.I * deriv F z := by
  change (starRingEnd ℂ)
      (F (star z) + Complex.I * deriv F (star z)) = _
  rw [map_add, map_mul, hF, Complex.conj_I]
  have hd := deriv_schwarz hF z
  change (starRingEnd ℂ) (deriv F (star z)) = deriv F z at hd
  rw [hd]
  have hs : (starRingEnd ℂ) (star (F z)) = F z := by
    exact star_star (F z)
  rw [hs]
  ring

/-- **Full-predicate derivative-companion bridge.**  For a
Schwarz-symmetric function, membership of `F + iF'` in the strict
Hermite--Biehler class is exactly derivative-companion norm dominance.
@isnad1 id=iff.1h1v.s6.f51f5ddfaae7 from=translated src=- shape=38b9b68a vocab=c2504369
-/
theorem hermiteBiehlerUHP_derivativeCompanion_iff
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, F (star z) = star (F z)) :
    HermiteBiehlerUHP (derivativeCompanionEntireFunction F) ↔
      DerivativeCompanionHermiteBiehlerUHP F := by
  constructor
  · intro h z hz
    simpa [DerivativeCompanionHermiteBiehlerAt,
      derivativeCompanionEntireFunction,
      hermiteBiehlerSharp_derivativeCompanionEntireFunction hF z] using h z hz
  · intro h z hz
    simpa [DerivativeCompanionHermiteBiehlerAt,
      derivativeCompanionEntireFunction,
      hermiteBiehlerSharp_derivativeCompanionEntireFunction hF z] using h z hz

/-- Therefore the full Hermite--Biehler inequality for the derivative
companion is exactly strict anti-Herglotz behavior of `F'/F`.
@isnad1 id=iff.1h1v.s6.8107e7c40e03 from=translated src=- shape=1c750d61 vocab=a9385a58
-/
theorem hermiteBiehlerUHP_derivativeCompanion_iff_strictAntiHerglotz
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, F (star z) = star (F z)) :
    HermiteBiehlerUHP (derivativeCompanionEntireFunction F) ↔
      StrictAntiHerglotzUHP (logDerivativeResponse F) :=
  (hermiteBiehlerUHP_derivativeCompanion_iff hF).trans
    (derivativeCompanionHermiteBiehlerUHP_iff_strictAntiHerglotz F)

/-- Evaluation of a real polynomial on `ℂ`.-/
noncomputable def realPolynomialComplexEval
    (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  (p.map (algebraMap ℝ ℂ)).eval z

/-- Evaluation of a real polynomial on `ℂ` obeys Schwarz reflection.
@isnad1 id=eq.0h2v.s6.ea5842764cae from=translated src=- shape=c3f23262 vocab=fb27ed5d
-/
theorem realPolynomialComplexEval_schwarz
    (p : Polynomial ℝ) (z : ℂ) :
    realPolynomialComplexEval p (star z) =
      star (realPolynomialComplexEval p z) := by
  simpa [realPolynomialComplexEval, Polynomial.aeval_def] using
    Polynomial.aeval_conj p z

/-- The analytic derivative of complex evaluation is evaluation of the
formal polynomial derivative.
@isnad1 id=eq.0h2v.s7.d6d7556fc9d7 from=translated src=- shape=bb0b3ac7 vocab=10b19a64
-/
theorem realPolynomialComplexEval_deriv
    (p : Polynomial ℝ) (z : ℂ) :
    deriv (realPolynomialComplexEval p) z =
      realPolynomialComplexEval p.derivative z := by
  change deriv (fun w : ℂ => (p.map (algebraMap ℝ ℂ)).eval w) z =
    (p.derivative.map (algebraMap ℝ ℂ)).eval z
  rw [Polynomial.deriv, Polynomial.derivative_map]

/-- At a real argument, complex evaluation is the complex embedding of real
evaluation.
@isnad1 id=eq.0h2v.s4.43d88319a822 from=translated src=- shape=71777729 vocab=817f581e
-/
theorem realPolynomialComplexEval_ofReal
    (p : Polynomial ℝ) (x : ℝ) :
    realPolynomialComplexEval p (x : ℂ) = Complex.ofReal (p.eval x) := by
  simp only [realPolynomialComplexEval]
  rw [Polynomial.eval_map]
  change Polynomial.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) x) p =
    (algebraMap ℝ ℂ) (p.eval x)
  rw [Polynomial.eval₂_at_apply]

/-- Function-level and polynomial logarithmic derivatives agree for complex
evaluation of a real polynomial.
@isnad1 id=eq.0h1v.s5.af1d38e56500 from=translated src=- shape=8aa0d1be vocab=f0ccae3b
-/
theorem logDerivativeResponse_realPolynomialComplexEval
    (p : Polynomial ℝ) :
    logDerivativeResponse (realPolynomialComplexEval p) =
      polynomialLogDerivResponse (p.map (algebraMap ℝ ℂ)) := by
  funext z
  simp only [logDerivativeResponse, polynomialLogDerivResponse]
  rw [realPolynomialComplexEval_deriv]
  simp [realPolynomialComplexEval, Polynomial.derivative_map]

/-- The normalized polynomial Hermite--Biehler candidate `A + iB`.-/
noncomputable def polynomialHermiteBiehlerFunction
    (A B : Polynomial ℝ) (z : ℂ) : ℂ :=
  realPolynomialComplexEval A z +
    Complex.I * realPolynomialComplexEval B z

/-- **Unconditional finite polynomial Hermite--Biehler criterion.**  For a
nonzero real polynomial `p`, the derivative companion `p+i p'` satisfies the
strict upper-half-plane Hermite--Biehler inequality exactly when `p` has
positive degree and every complex root of `p` is real.  This theorem is
proved from the repository's polynomial anti-Herglotz equivalence and does
not consume `NormalizedPolynomialHermiteBiehlerTheoremData`.
@isnad1 id=iff.1h1v.s6.cea2d60fa7d3 from=translated src=- shape=e23eca51 vocab=9f20df0b
-/
theorem realPolynomial_derivativeCompanion_hermiteBiehler_iff_roots_real
    (p : Polynomial ℝ) (hp : p ≠ 0) :
    HermiteBiehlerUHP
        (derivativeCompanionEntireFunction (realPolynomialComplexEval p)) ↔
      0 < p.natDegree ∧
        ∀ ρ : ℂ, realPolynomialComplexEval p ρ = 0 → ρ.im = 0 := by
  let q : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hp
  have hschwarz : ∀ z : ℂ,
      realPolynomialComplexEval p (star z) =
        star (realPolynomialComplexEval p z) :=
    realPolynomialComplexEval_schwarz p
  rw [hermiteBiehlerUHP_derivativeCompanion_iff_strictAntiHerglotz hschwarz]
  rw [logDerivativeResponse_realPolynomialComplexEval]
  rw [polynomial_strictAntiHerglotz_iff_roots_real q hq]
  · simp only [q, Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective ℝ ℂ)]
    rfl
  · intro z
    simpa [q, realPolynomialComplexEval] using
      realPolynomialComplexEval_schwarz p z

/-- Exact value of the polynomial derivative companion on the real axis.
@isnad1 id=eq.0h2v.s7.89765e7b4d84 from=translated src=- shape=fde3bcee vocab=73dcdef7
-/
theorem derivativeCompanion_realPolynomial_at_real
    (p : Polynomial ℝ) (x : ℝ) :
    derivativeCompanionEntireFunction (realPolynomialComplexEval p) (x : ℂ) =
      Complex.ofReal (p.eval x) +
        Complex.I * Complex.ofReal (p.derivative.eval x) := by
  rw [derivativeCompanionEntireFunction,
    realPolynomialComplexEval_deriv]
  simp only [realPolynomialComplexEval]
  rw [Polynomial.eval_map, Polynomial.eval_map]
  change
    Polynomial.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) x) p +
        Complex.I *
          Polynomial.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) x) p.derivative =
      (algebraMap ℝ ℂ) (p.eval x) +
        Complex.I * (algebraMap ℝ ℂ) (p.derivative.eval x)
  rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]

/-- On the real axis, the derivative companion is nonzero exactly when `p`
and `p'` do not vanish simultaneously.
@isnad1 id=iff.0h2v.s7.dd25c7a299b1 from=translated src=- shape=51c9e245 vocab=bab42821
-/
theorem derivativeCompanion_realPolynomial_ne_zero_iff
    (p : Polynomial ℝ) (x : ℝ) :
    derivativeCompanionEntireFunction (realPolynomialComplexEval p) (x : ℂ) ≠ 0 ↔
      ¬ (p.eval x = 0 ∧ p.derivative.eval x = 0) := by
  rw [derivativeCompanion_realPolynomial_at_real]
  apply not_congr
  constructor
  · intro h
    constructor
    · have hre := congrArg Complex.re h
      simpa using hre
    · have him := congrArg Complex.im h
      simpa using him
  · rintro ⟨hA, hB⟩
    simp [hA, hB]

/-- The strict no-real-zero version exposes the additional no-common-root
condition explicitly.  Thus real-rootedness is not conflated with
simplicity.
@isnad1 id=iff.1h1v.s7.7878068ff0c1 from=translated src=- shape=afd1ae39 vocab=8a1b0382
-/
theorem
    realPolynomial_derivativeCompanion_hermiteBiehlerNoRealZeros_iff
    (p : Polynomial ℝ) (hp : p ≠ 0) :
    HermiteBiehlerNoRealZeros
        (derivativeCompanionEntireFunction (realPolynomialComplexEval p)) ↔
      0 < p.natDegree ∧
        (∀ ρ : ℂ, realPolynomialComplexEval p ρ = 0 → ρ.im = 0) ∧
        ∀ x : ℝ, ¬ (p.eval x = 0 ∧ p.derivative.eval x = 0) := by
  rw [HermiteBiehlerNoRealZeros,
    realPolynomial_derivativeCompanion_hermiteBiehler_iff_roots_real p hp]
  constructor
  · rintro ⟨⟨hdeg, hreal⟩, hno⟩
    exact ⟨hdeg, hreal, fun x =>
      (derivativeCompanion_realPolynomial_ne_zero_iff p x).mp (hno x)⟩
  · rintro ⟨hdeg, hreal, hno⟩
    exact ⟨⟨hdeg, hreal⟩, fun x =>
      (derivativeCompanion_realPolynomial_ne_zero_iff p x).mpr (hno x)⟩

/-- Oriented strict interlacing factorization data proves the real-axis
nonvanishing part of Hermite--Biehler directly.  The remaining deep reverse
direction is only the open-upper-half-plane norm inequality.
@isnad1 id=ne.0h4v.s4.000235b7b7fd from=translated src=- shape=61486e26 vocab=e04a7147
-/
theorem OrientedStrictInterlacingPolynomialData.polynomialHermiteBiehler_noRealZeros
    {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) :
    ∀ x : ℝ, polynomialHermiteBiehlerFunction A B (x : ℂ) ≠ 0 := by
  intro x hzero
  apply D.no_common_real_root x
  constructor
  · have hre := congrArg Complex.re hzero
    simpa [polynomialHermiteBiehlerFunction,
      realPolynomialComplexEval_ofReal] using hre
  · have him := congrArg Complex.im hzero
    simpa [polynomialHermiteBiehlerFunction,
      realPolynomialComplexEval_ofReal] using him

/-- **Interface for the full normalized polynomial Hermite--Biehler
theorem.**  Under the visible degree and nonzero conditions, the strict
upper-half-plane norm inequality **plus absence of real zeros of `A+iB`** is
equivalent to complete, oriented, simple interlacing factorization data.

This interface is deliberately a structure.  Constructing a value requires
formalizing both deep classical implications; merely importing this file
does not assume either implication.-/
structure NormalizedPolynomialHermiteBiehlerTheoremData : Prop where
  forward :
    ∀ A B : Polynomial ℝ,
      A ≠ 0 → B ≠ 0 → A.natDegree = B.natDegree + 1 →
      HermiteBiehlerNoRealZeros (polynomialHermiteBiehlerFunction A B) →
      Nonempty (OrientedStrictInterlacingPolynomialData A B)
  reverse :
    ∀ A B : Polynomial ℝ,
      A ≠ 0 → B ≠ 0 → A.natDegree = B.natDegree + 1 →
      Nonempty (OrientedStrictInterlacingPolynomialData A B) →
      HermiteBiehlerNoRealZeros (polynomialHermiteBiehlerFunction A B)

/-- The exact iff obtained from an explicit implementation of the classical
normalized polynomial Hermite--Biehler theorem.
@isnad1 id=iff.4h2v.s6.8370c1d425bc from=translated src=- shape=b0b6cb8d vocab=b26b2fb4
-/
theorem normalizedPolynomialHermiteBiehler_iff_interlacing
    (T : NormalizedPolynomialHermiteBiehlerTheoremData)
    (A B : Polynomial ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree = B.natDegree + 1) :
    HermiteBiehlerNoRealZeros (polynomialHermiteBiehlerFunction A B) ↔
      Nonempty (OrientedStrictInterlacingPolynomialData A B) :=
  ⟨T.forward A B hA hB hdeg, T.reverse A B hA hB hdeg⟩

/-! ## Full function-level interlacing interface -/

/-- The entire-function Hermite--Biehler candidate `A+iB`.-/
def entireHermiteBiehlerFunction
    (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  A z + Complex.I * B z

/-- **Pair-specific interface for the full entire Hermite--Biehler
interlacing theorem.**  The forward field extracts an exhaustive,
integer-indexed, simple, oriented bi-infinite alternation of the zeros of `A`
and `B` from the upper-half-plane norm inequality together with absence of
real zeros; the reverse field proves both properties from that complete data.

The pair-specific form is intentional.  For general entire functions the
converse requires additional bounded-type/growth hypotheses, and those are
not available in pinned Mathlib.  An inhabitant can therefore be constructed
only after the necessary classical hypotheses for the concrete pair have
been discharged.-/
structure EntireHermiteBiehlerInterlacingTheoremData
    (A B : ℂ → ℂ) : Prop where
  forward :
    HermiteBiehlerNoRealZeros (entireHermiteBiehlerFunction A B) →
      Nonempty (OrientedEntireBiInfiniteStrictInterlacingData A B)
  reverse :
    Nonempty (OrientedEntireBiInfiniteStrictInterlacingData A B) →
      HermiteBiehlerNoRealZeros (entireHermiteBiehlerFunction A B)

/-- Exact full function-level Hermite--Biehler/interlacing equivalence from
an explicitly supplied proof package.
@isnad1 id=iff.1h2v.s4.ceb8d32d7a5b from=translated src=- shape=46371d65 vocab=9eda935b
-/
theorem entireHermiteBiehler_iff_orientedStrictInterlacing
    {A B : ℂ → ℂ}
    (T : EntireHermiteBiehlerInterlacingTheoremData A B) :
    HermiteBiehlerNoRealZeros (entireHermiteBiehlerFunction A B) ↔
      Nonempty (OrientedEntireBiInfiniteStrictInterlacingData A B) :=
  ⟨T.forward, T.reverse⟩

end OverflowResidueRH
