/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.Divisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A rational function is determined up to a unit by its divisor

Building on `EllipticCurves.FunctionField.Divisors` (the order-of-vanishing / divisor calculus on
the function field `F(W) = Frac F[W]` of a Weierstrass curve whose coordinate ring is a Dedekind
domain), this file proves the **well-definedness backbone** of the divisor-theoretic Weil pairing
(project issue #244): on `F(W)` a rational function is determined, up to a unit of the coordinate
ring `F[W]`, by its divisor.

Concretely, if two nonzero `f, g ∈ F(W)` have the same order of vanishing at every closed point
(`∀ v, ord v f = ord v g`, equivalently `divisor W f = divisor W g`), then `f = u • g` for some
unit `u : F[W]ˣ`. This is exactly what makes the generator `f_P` — produced by the rung-1
principal-ideal statement `XYIdeal'_pow_isPrincipal_of_torsion` (issue #401), with
`div f_P = n·(P) − n·(O)` — canonical up to scalar, as the pairing `e_n(S, T)` requires.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.eq_of_count_eq` : count-injectivity of **nonzero fractional
  ideals** over any Dedekind domain — if `count v I = count v J` for every height-one prime `v`,
  then `I = J`. (General; a Mathlib gap-filler, upstream candidate.)
* `WeierstrassCurve.Affine.spanSingleton_eq_of_ord_eq` : equal orders everywhere give equal
  principal fractional ideals `⟨f⟩ = ⟨g⟩`.
* `WeierstrassCurve.Affine.exists_unit_of_ord_eq` / `exists_unit_of_divisor_eq` : two nonzero
  rational functions with the same orders (equivalently the same `divisor`) differ by a unit of
  `F[W]`.

## Design

Everything carries the explicit hypothesis `[IsDedekindDomain W.CoordinateRing]`, exactly as in
`Divisors.lean` / `DivisorClassGroup.lean`, decoupling the development from the Part A normality
discharge of issue #396. It is likewise independent of the elliptic-net (Ward) recurrence.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (a rational function is determined up to an
`F*`-scalar by its divisor — Abel's theorem) and III.8 (the Weil pairing).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Count-injectivity of nonzero fractional ideals.** A nonzero fractional ideal is recovered
from its `count` (the `v`-adic multiplicities `∏ᶠ v, v ^ count v I`), so two nonzero fractional
ideals with equal counts at every height-one prime are equal. -/
theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
      ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- Two nonzero rational functions with the same order of vanishing at every closed point generate
the same principal fractional ideal of `F[W]`. -/
theorem spanSingleton_eq_of_ord_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v, ord v f = ord v g) :
    spanSingleton W.CoordinateRing⁰ f = spanSingleton W.CoordinateRing⁰ g := by
  have hf' : spanSingleton W.CoordinateRing⁰ f ≠ 0 := by rwa [ne_eq, spanSingleton_eq_zero_iff]
  have hg' : spanSingleton W.CoordinateRing⁰ g ≠ 0 := by rwa [ne_eq, spanSingleton_eq_zero_iff]
  exact eq_of_count_eq hf' hg' h

/-- **The divisor determines a rational function up to a unit** (order form). If nonzero
`f, g ∈ F(W)` have the same order of vanishing at every closed point, they differ by a unit of the
coordinate ring `F[W]`: `u • f = g` for some `u : F[W]ˣ`. -/
theorem exists_unit_of_ord_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v, ord v f = ord v g) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • f = g :=
  (spanSingleton_eq_spanSingleton (S := W.CoordinateRing⁰) (P := W.FunctionField)).mp
    (spanSingleton_eq_of_ord_eq hf hg h)

/-- **The divisor determines a rational function up to a unit** (divisor form). If nonzero
`f, g ∈ F(W)` have the same divisor, they differ by a unit of `F[W]`. -/
theorem exists_unit_of_divisor_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisor W f = divisor W g) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • f = g := by
  refine exists_unit_of_ord_eq hf hg fun v => ?_
  have := DFunLike.congr_fun h v
  rwa [divisor_apply, divisor_apply] at this

end WeierstrassCurve.Affine
