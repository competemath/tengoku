/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Divisors and orders of vanishing on a Weierstrass curve

For a Weierstrass curve `W` over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain, this file builds the **order-of-vanishing calculus** on the function field
`F(W) = Frac F[W]`, together with the (finitely-supported) **divisor** of a rational function.

The closed points of the affine curve are exactly the height-one primes of `F[W]`,
i.e. `IsDedekindDomain.HeightOneSpectrum F[W]`. Given such a point `v`, the order of vanishing
`ord v f` of a rational function `f ∈ F(W)` is Mathlib's `FractionalIdeal.count`, applied to the
principal fractional ideal `⟨f⟩`. All the divisor bookkeeping — additivity under multiplication,
the values at `0`, `1`, inverses — is then a direct consequence of the corresponding facts about
`FractionalIdeal.count`, which is a homomorphism from the group of nonzero fractional ideals.

## Design / the Dedekind hypothesis

The whole development is stated under an explicit hypothesis `[IsDedekindDomain W.CoordinateRing]`.
On a **nonsingular** Weierstrass curve this holds: the two unconditional Dedekind pillars
(Noetherian, Krull dimension `≤ 1`) are `EllipticCurves.Torsion.CoordinateRingDedekind`, and the
remaining integrally-closed (normality) input follows from nonsingularity. ⚠️ That discharge is
**done, and is a global instance**: `instIsDedekindDomain` of
`EllipticCurves.FunctionField.CoordinateRingNormalGeneral` supplies
`[IsDedekindDomain W.CoordinateRing]` for every `[W.IsElliptic]` over an **arbitrary** field, with
no `[IsAlgClosed F]` — so for an elliptic curve the hypothesis carried throughout this file is a
binder, not an obligation. Keeping it as a
hypothesis here decouples the divisor calculus from the normality discharge, so the divisor layer
is available to any consumer that supplies (or assumes) Dedekindness. This is the divisor / order
substrate the divisor-theoretic Weil pairing (issue #244) is built on.

## Main definitions

* `WeierstrassCurve.Affine.ord v f` : the order of vanishing of `f ∈ F(W)` at the closed point `v`.
* `WeierstrassCurve.Affine.divisor f : HeightOneSpectrum F[W] →₀ ℤ` : the divisor of `f`, i.e.
  the finitely-supported function `v ↦ ord v f`.

## Main statements

* `ord_mul`, `ord_one`, `ord_zero`, `ord_inv`, `ord_pow`, `ord_zpow` : `ord v` is (on nonzero
  arguments) a homomorphism `F(W)ˣ → ℤ`.
* `divisor_mul`, `divisor_one`, `divisor_zero`, `divisor_inv` : the same, packaged as the
  `Finsupp`-valued divisor.

## A deliberate omission: degrees

The classical identity `deg (div f) = 0` (principal divisors have degree zero) is a statement about
the **projective/complete** curve: on the affine chart the poles of `f` at the point(s) at infinity
are invisible, so `∑ v, ord v f` (suitably weighted by residue degrees) is *not* zero in general.
Degrees are therefore not developed here; they belong to the projective completion and are left to
a downstream file. ⚠️ That file exists, and there are two of them:
`EllipticCurves.FunctionField.DivisorDegree` builds `degPt` and `degDiv` and proves
`degDiv (div f) + ordInfty f = 0`, and `EllipticCurves.FunctionField.ProjectiveDivisor` puts the
affine orders and `ordInfty` on one object and states the same theorem as
`degProj (divisorProj f) = 0`. Both are downstream of this file, so no declaration here can name
either; the omission is scope, and the pointer is what the sentence was missing.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors on curves) and III.8 (the Weil
pairing).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  (v : HeightOneSpectrum W.CoordinateRing)

/-- The **order of vanishing** of a rational function `f ∈ F(W)` at the closed point `v` (a
height-one prime of the coordinate ring `F[W]`). It is `FractionalIdeal.count` of the principal
fractional ideal `⟨f⟩`; equivalently `−` the `v`-adic valuation of `f`, valued in `ℤ` with the
convention `ord v 0 = 0`. -/
noncomputable def ord (f : W.FunctionField) : ℤ :=
  FractionalIdeal.count W.FunctionField v (spanSingleton W.CoordinateRing⁰ f)

@[simp]
lemma ord_zero : ord v (0 : W.FunctionField) = 0 := by
  rw [ord, spanSingleton_zero, count_zero]

@[simp]
lemma ord_one : ord v (1 : W.FunctionField) = 0 := by
  rw [ord, spanSingleton_one, count_one]

lemma ord_mul {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  have hf' : spanSingleton W.CoordinateRing⁰ f ≠ 0 := by
    rwa [ne_eq, spanSingleton_eq_zero_iff]
  have hg' : spanSingleton W.CoordinateRing⁰ g ≠ 0 := by
    rwa [ne_eq, spanSingleton_eq_zero_iff]
  rw [ord, ord, ord, ← spanSingleton_mul_spanSingleton, count_mul _ _ hf' hg']

@[simp]
lemma ord_inv (f : W.FunctionField) : ord v f⁻¹ = -ord v f := by
  rw [ord, ord, ← spanSingleton_inv, count_inv]

lemma ord_div {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f / g) = ord v f - ord v g := by
  rw [div_eq_mul_inv, ord_mul v hf (inv_ne_zero hg), ord_inv, sub_eq_add_neg]

lemma ord_pow (f : W.FunctionField) (n : ℕ) : ord v (f ^ n) = n * ord v f := by
  rw [ord, ord, ← spanSingleton_pow, count_pow]

lemma ord_zpow (f : W.FunctionField) (n : ℤ) : ord v (f ^ n) = n * ord v f := by
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, ord_pow]
  | negSucc k =>
    rw [zpow_negSucc, ord_inv, ord_pow, Int.negSucc_eq]
    push_cast; ring

/-- The order-of-vanishing function `v ↦ ord v f` has finite support: a rational function has
zeros and poles at only finitely many closed points. -/
lemma ord_finite (f : W.FunctionField) :
    (Function.support fun v : HeightOneSpectrum W.CoordinateRing => ord v f).Finite :=
  Filter.eventually_cofinite.mp (finite_factors (spanSingleton W.CoordinateRing⁰ f))

variable (W) in
/-- The **divisor** of a rational function `f ∈ F(W)`: the finitely-supported map sending each
closed point `v` to the order of vanishing `ord v f`. -/
noncomputable def divisor (f : W.FunctionField) : HeightOneSpectrum W.CoordinateRing →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => ord v f) (ord_finite f)

@[simp]
lemma divisor_apply (f : W.FunctionField) (v : HeightOneSpectrum W.CoordinateRing) :
    divisor W f v = ord v f :=
  rfl

@[simp]
lemma divisor_zero : divisor W (0 : W.FunctionField) = 0 := by
  ext v; simp

@[simp]
lemma divisor_one : divisor W (1 : W.FunctionField) = 0 := by
  ext v; simp

lemma divisor_mul {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor W (f * g) = divisor W f + divisor W g := by
  ext v; simp [ord_mul v hf hg]

@[simp]
lemma divisor_inv (f : W.FunctionField) : divisor W f⁻¹ = -divisor W f := by
  ext v; simp

lemma divisor_div {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor W (f / g) = divisor W f - divisor W g := by
  ext v; simp [ord_div v hf hg, sub_eq_add_neg]

end WeierstrassCurve.Affine
