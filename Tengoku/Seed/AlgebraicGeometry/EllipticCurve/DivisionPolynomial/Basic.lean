/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Tengoku.Seed.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves.
These are defined in terms of the auxiliary sequences for normalised elliptic divisibility sequences
(EDS) as defined in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. The sequence of `n`-division polynomials
`ψₙ ∈ R[X, Y]` of `W` is the normalised EDS with initial values
* `ψ₀ := 0`,
* `ψ₁ := 1`,
* `ψ₂ := 2Y + a₁X + a₃`,
* `ψ₃ := 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and
* `ψ₄ := ψ₂ ⬝ (2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²))`.

Furthermore, define the associated sequences `φₙ, ωₙ ∈ R[X, Y]` by
* `φₙ := Xψₙ² - ψₙ₊₁ ⬝ ψₙ₋₁`, and
* `ωₙ := (ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2`.

Note that `ωₙ` is always well-defined as a polynomial in `R[X, Y]`. As a start, it can be shown by
induction that `ψₙ` always divides `ψ₂ₙ` in `R[X, Y]`, so that `ψ₂ₙ / ψₙ` is always well-defined as
a polynomial, while division by `2` is well-defined when `R` has characteristic different from `2`.
In general, it can be shown that `2` always divides the polynomial `ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)`
in the characteristic `0` universal ring `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` of `W`, where the
`Aᵢ` are indeterminates. Then `ωₙ` can be equivalently defined as the image of this division under
the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`.

Now, in the coordinate ring `R[W]`, note that `ψ₂²` is congruent to the polynomial
`Ψ₂Sq := 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`. As such, the recurrences of a normalised EDS show that
`ψₙ / ψ₂` are congruent to certain polynomials in `R[W]`. In particular, define `preΨₙ ∈ R[X]` as
the auxiliary sequence for a normalised EDS with extra parameter `Ψ₂Sq²` and initial values
* `preΨ₀ := 0`,
* `preΨ₁ := 1`,
* `preΨ₂ := 1`,
* `preΨ₃ := ψ₃`, and
* `preΨ₄ := ψ₄ / ψ₂`.

The corresponding normalised EDS `Ψₙ ∈ R[X, Y]` is then given by
* `Ψₙ := preΨₙ ⬝ ψ₂` if `n` is even, and
* `Ψₙ := preΨₙ` if `n` is odd.

Furthermore, define the associated sequences `ΨSqₙ, Φₙ ∈ R[X]` by
* `ΨSqₙ := preΨₙ² ⬝ Ψ₂Sq` if `n` is even,
* `ΨSqₙ := preΨₙ²` if `n` is odd,
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁` if `n` is even, and
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁ ⬝ Ψ₂Sq` if `n` is odd.

With these definitions, `ψₙ ∈ R[X, Y]` and `φₙ ∈ R[X, Y]` are congruent in `R[W]` to `Ψₙ ∈ R[X, Y]`
and `Φₙ ∈ R[X]` respectively, which are defined in terms of `Ψ₂Sq ∈ R[X]` and `preΨₙ ∈ R[X]`.

## Main definitions

* `WeierstrassCurve.preΨ`: the univariate polynomials `preΨₙ`.
* `WeierstrassCurve.ΨSq`: the univariate polynomials `ΨSqₙ`.
* `WeierstrassCurve.Ψ`: the bivariate polynomials `Ψₙ`.
* `WeierstrassCurve.Φ`: the univariate polynomials `Φₙ`.
* `WeierstrassCurve.ψ`: the bivariate `n`-division polynomials `ψₙ`.
* `WeierstrassCurve.φ`: the bivariate polynomials `φₙ`.
* TODO: the bivariate polynomials `ωₙ`.

## Implementation notes

Analogously to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, the bivariate polynomials
`Ψₙ` are defined in terms of the univariate polynomials `preΨₙ`. This is done partially to avoid
ring division, but more crucially to allow the definition of `ΨSqₙ` and `Φₙ` as univariate
polynomials without needing to work under the coordinate ring, and to allow the computation of their
leading terms without ambiguity. Furthermore, evaluating these polynomials at a rational point on
`W` recovers their original definition up to linear combinations of the Weierstrass equation of `W`,
hence also avoiding the need to work in the coordinate ring.

TODO: implementation notes for the definition of `ωₙ`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

section Ψ₂Sq

/-! ### The univariate polynomial `Ψ₂Sq` -/

/-- The `2`-division polynomial `ψ₂ = Ψ₂`. -/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

/-- The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

/--
@isnad1 id=eq.0h2v.s9.46e9b4392f6b from=seed src=0 shape=767e33c4 vocab=202cc4fb
-/
lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1

/--
@isnad1 id=eq.0h2v.s9.14d97fc96086 from=seed src=0 shape=c9bb10d1 vocab=843054c7
-/
lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial := by
  simp [C_Ψ₂Sq]

/--
@isnad1 id=eq.0h2v.s9.c5a1225f1d2d from=seed src=0 shape=141123c3 vocab=fc1497ca
-/
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`
/--
@isnad1 id=eq.0h2v.s4.76976c0b0212 from=seed src=0 shape=27b1f6da vocab=28463aa6
-/
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

end Ψ₂Sq

section preΨ'

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℕ` -/

/-- The `3`-division polynomial `ψ₃ = Ψ₃`. -/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/-- The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ψ₂`. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

/--
@isnad1 id=eq.0h2v.s5.4fb6730de10d from=seed src=0 shape=217e3f21 vocab=6ffed15c
-/
@[simp]
lemma preΨ'_zero : W.preΨ' 0 = 0 :=
  preNormEDS'_zero ..

/--
@isnad1 id=eq.0h2v.s5.22b5c286b501 from=seed src=0 shape=217e3f21 vocab=6ffed15c
-/
@[simp]
lemma preΨ'_one : W.preΨ' 1 = 1 :=
  preNormEDS'_one ..

/--
@isnad1 id=eq.0h2v.s5.8440ec9e4c57 from=seed src=0 shape=217e3f21 vocab=6ffed15c
-/
@[simp]
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..

/--
@isnad1 id=eq.0h2v.s4.82023b34a0dc from=seed src=0 shape=85bd6e34 vocab=98a1f3ad
-/
@[simp]
lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=
  preNormEDS'_three ..

/--
@isnad1 id=eq.0h2v.s4.911bacde7349 from=seed src=0 shape=85bd6e34 vocab=fce8e997
-/
@[simp]
lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ :=
  preNormEDS'_four ..

/--
@isnad1 id=eq.0h3v.s8.4a5062ce84fc from=seed src=0 shape=cfa18a15 vocab=bf56c09f
-/
lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..

/--
@isnad1 id=eq.0h3v.s9.06cf23ebdac3 from=seed src=0 shape=5ff101a4 vocab=150aea2d
-/
lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..

end preΨ'

section preΨ

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℤ` -/

/-- The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

/--
@isnad1 id=eq.0h3v.s4.81a58338f232 from=seed src=0 shape=307e489f vocab=8e6a32c8
-/
@[simp]
lemma preΨ_ofNat (n : ℕ) : W.preΨ n = W.preΨ' n :=
  preNormEDS_ofNat ..

/--
@isnad1 id=eq.0h2v.s5.54a2b15bc424 from=seed src=0 shape=217e3f21 vocab=68464376
-/
@[simp]
lemma preΨ_zero : W.preΨ 0 = 0 :=
  preNormEDS_zero ..

/--
@isnad1 id=eq.0h2v.s5.bf8afb112da5 from=seed src=0 shape=217e3f21 vocab=68464376
-/
@[simp]
lemma preΨ_one : W.preΨ 1 = 1 :=
  preNormEDS_one ..

/--
@isnad1 id=eq.0h2v.s5.743762d35e87 from=seed src=0 shape=217e3f21 vocab=68464376
-/
@[simp]
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..

/--
@isnad1 id=eq.0h2v.s4.ee01bf189e30 from=seed src=0 shape=85bd6e34 vocab=f460bb15
-/
@[simp]
lemma preΨ_three : W.preΨ 3 = W.Ψ₃ :=
  preNormEDS_three ..

/--
@isnad1 id=eq.0h2v.s4.0baf162bbbc0 from=seed src=0 shape=85bd6e34 vocab=f5644571
-/
@[simp]
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..

/--
@isnad1 id=eq.0h3v.s5.bcf2ce837368 from=seed src=0 shape=c2a504ac vocab=3199821c
-/
@[simp]
lemma preΨ_neg (n : ℤ) : W.preΨ (-n) = -W.preΨ n :=
  preNormEDS_neg ..

/--
@isnad1 id=eq.0h3v.s8.8c1ce762934e from=seed src=0 shape=15ce628a vocab=90229a06
-/
lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..

/--
@isnad1 id=eq.0h3v.s9.50447207a9dd from=seed src=0 shape=79290dc4 vocab=4f9b240c
-/
lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =
    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd ..

end preΨ

section ΨSq

/-! ### The univariate polynomials `ΨSqₙ` -/

/-- The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`. -/
noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

/--
@isnad1 id=eq.0h3v.s7.be4d4314af96 from=seed src=0 shape=4996176b vocab=76ec60d1
-/
@[simp]
lemma ΨSq_ofNat (n : ℕ) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp [ΨSq]

/--
@isnad1 id=eq.0h2v.s5.0c913994f1ec from=seed src=0 shape=217e3f21 vocab=de8b0ec2
-/
@[simp]
lemma ΨSq_zero : W.ΨSq 0 = 0 := by
  simp [ΨSq]

/--
@isnad1 id=eq.0h2v.s5.00dbf4b99afb from=seed src=0 shape=217e3f21 vocab=de8b0ec2
-/
@[simp]
lemma ΨSq_one : W.ΨSq 1 = 1 := by
  simp [ΨSq]

/--
@isnad1 id=eq.0h2v.s4.cad46bda8267 from=seed src=0 shape=85bd6e34 vocab=515c94f7
-/
@[simp]
lemma ΨSq_two : W.ΨSq 2 = W.Ψ₂Sq := by
  simp [ΨSq]

/--
@isnad1 id=eq.0h2v.s6.6904723130c5 from=seed src=0 shape=4d5fd093 vocab=1bc2cd9e
-/
@[simp]
lemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 := by
  simp [ΨSq, show ¬Even (3 : ℤ) by decide]

/--
@isnad1 id=eq.0h2v.s7.d9cdfd86f540 from=seed src=0 shape=2074e495 vocab=a2bee8f8
-/
@[simp]
lemma ΨSq_four : W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq := by
  simp [ΨSq, show ¬Odd (4 : ℤ) by decide]

/--
@isnad1 id=eq.0h3v.s4.90a264eafffc from=seed src=0 shape=adcb709e vocab=ca319998
-/
@[simp]
lemma ΨSq_neg (n : ℤ) : W.ΨSq (-n) = W.ΨSq n := by
  simp [ΨSq]

/--
@isnad1 id=eq.0h3v.s9.32df61e661c2 from=seed src=0 shape=be687ae1 vocab=607006b6
-/
lemma ΨSq_even (m : ℤ) : W.ΨSq (2 * m) =
    (W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2 * W.Ψ₂Sq := by
  rw [ΨSq, preΨ_even, ite_eq_left <| even_two_mul m]

/--
@isnad1 id=eq.0h3v.s9.9269d598ee1d from=seed src=0 shape=4a9bc894 vocab=3069dd76
-/
lemma ΨSq_odd (m : ℤ) : W.ΨSq (2 * m + 1) =
    (W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  rw [ΨSq, preΨ_odd, ite_eq_right m.not_even_two_mul_add_one, mul_one]

end ΨSq

section Ψ

/-! ### The bivariate polynomials `Ψₙ` -/

/-- The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

open WeierstrassCurve (Ψ)

/--
@isnad1 id=eq.0h3v.s8.64094ac13ce6 from=seed src=0 shape=300bcff0 vocab=7e22dc4f
-/
@[simp]
lemma Ψ_ofNat (n : ℕ) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp [Ψ]

/--
@isnad1 id=eq.0h2v.s6.a06a3aefb4e6 from=seed src=0 shape=e8ed2977 vocab=475fb25a
-/
@[simp]
lemma Ψ_zero : W.Ψ 0 = 0 := by
  simp [Ψ]

/--
@isnad1 id=eq.0h2v.s6.00862a520331 from=seed src=0 shape=e8ed2977 vocab=475fb25a
-/
@[simp]
lemma Ψ_one : W.Ψ 1 = 1 := by
  simp [Ψ]

/--
@isnad1 id=eq.0h2v.s5.8b5f1fc5112e from=seed src=0 shape=6b074847 vocab=0f4fd9eb
-/
@[simp]
lemma Ψ_two : W.Ψ 2 = W.ψ₂ := by
  simp [Ψ]

/--
@isnad1 id=eq.0h2v.s7.8e6f839ddf99 from=seed src=0 shape=36cc48d6 vocab=61e39c29
-/
@[simp]
lemma Ψ_three : W.Ψ 3 = C W.Ψ₃ := by
  simp [Ψ, show ¬Even (3 : ℤ) by decide]

/--
@isnad1 id=eq.0h2v.s8.c19eb1d74de0 from=seed src=0 shape=40e7cc17 vocab=4232cf49
-/
@[simp]
lemma Ψ_four : W.Ψ 4 = C W.preΨ₄ * W.ψ₂ := by
  simp [Ψ, show ¬Odd (4 : ℤ) by decide]

/--
@isnad1 id=eq.0h3v.s6.71a764d19035 from=seed src=0 shape=7604a9b7 vocab=ac2d52f0
-/
@[simp]
lemma Ψ_neg (n : ℤ) : W.Ψ (-n) = -W.Ψ n := by
  simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]

/--
@isnad1 id=eq.0h3v.s9.3ed10ca2d84f from=seed src=0 shape=025c49c3 vocab=4cec9aa0
-/
lemma Ψ_even (m : ℤ) : W.Ψ (2 * m) * W.ψ₂ =
    W.Ψ (m - 1) ^ 2 * W.Ψ m * W.Ψ (m + 2) - W.Ψ (m - 2) * W.Ψ m * W.Ψ (m + 1) ^ 2 := by
  simp_rw [Ψ, preΨ_even, ite_eq_left <| even_two_mul m, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> ring1

/--
@isnad1 id=eq.0h3v.s10.63f46d759404 from=seed src=0 shape=8156292f vocab=5310f1e6
-/
lemma Ψ_odd (m : ℤ) : W.Ψ (2 * m + 1) =
    W.Ψ (m + 2) * W.Ψ m ^ 3 - W.Ψ (m - 1) * W.Ψ (m + 1) ^ 3 +
      W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) *
        C (if Even m then W.preΨ (m + 2) * W.preΨ m ^ 3
            else -W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3) := by
  simp_rw [Ψ, preΨ_odd, ite_eq_right m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

/--
@isnad1 id=eq.0h3v.s9.396570f1b948 from=seed src=0 shape=a9acd936 vocab=f5bdd981
-/
lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]

end Ψ

section Φ

/-! ### The univariate polynomials `Φₙ` -/

/-- The univariate polynomials `Φₙ` congruent to `φₙ`. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

open WeierstrassCurve (Φ)

/--
@isnad1 id=eq.0h3v.s8.17584ec7a17a from=seed src=0 shape=f7f3e2ea vocab=5f8297ec
-/
@[simp]
lemma Φ_ofNat (n : ℕ) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  rw [Φ, add_sub_cancel_right]
  norm_cast
  simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]

/--
@isnad1 id=eq.0h2v.s5.1e2ab10e7f9e from=seed src=0 shape=217e3f21 vocab=3f30e938
-/
@[simp]
lemma Φ_zero : W.Φ 0 = 1 := by
  simp [Φ]

/--
@isnad1 id=eq.0h2v.s5.bd4f8b3842f3 from=seed src=0 shape=9a1f6691 vocab=781e0ad0
-/
@[simp]
lemma Φ_one : W.Φ 1 = X := by
  simp [Φ]

/--
@isnad1 id=eq.0h2v.s9.f3391cad35d4 from=seed src=0 shape=f6338291 vocab=4362228e
-/
@[simp]
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  rw [show 2 = ((1 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_two, ite_eq_right Nat.not_even_one, Ψ₂Sq,
    preΨ'_three, preΨ'_one, ite_eq_right Nat.not_even_one, Ψ₃]
  C_simp
  ring1

/--
@isnad1 id=eq.0h2v.s7.f263f10c61ab from=seed src=0 shape=3ba4e656 vocab=af39cf69
-/
@[simp]
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by
  rw [show 3 = ((2 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_three, ite_eq_left <| by decide, mul_one,
    preΨ'_four, preΨ'_two, mul_one, ite_eq_left even_two]

/--
@isnad1 id=eq.0h2v.s8.ca69f2e7fb1c from=seed src=0 shape=a21f8f10 vocab=af39cf69
-/
@[simp]
lemma Φ_four : W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  rw [show 4 = ((3 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_four, ite_eq_right <| by decide,
    show 3 + 2 = 2 * 2 + 1 by rfl, preΨ'_odd, preΨ'_four, preΨ'_two, ite_eq_left Even.zero,
    preΨ'_one, preΨ'_three, ite_eq_left Even.zero, ite_eq_right <| by decide]
  ring1

/--
@isnad1 id=eq.0h3v.s4.1b6b80cf6ded from=seed src=0 shape=adcb709e vocab=a34addff
-/
@[simp]
lemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n := by
  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,
    neg_mul_neg, mul_comm <| W.preΨ <| n - 1, even_neg]

end Φ

section ψ

/-! ### The bivariate polynomials `ψₙ` -/

/-- The bivariate `n`-division polynomials `ψₙ`. -/
protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

open WeierstrassCurve (Ψ ψ)

/--
@isnad1 id=eq.0h2v.s6.1748faf985b1 from=seed src=0 shape=e8ed2977 vocab=aa4cf41c
-/
@[simp]
lemma ψ_zero : W.ψ 0 = 0 :=
  normEDS_zero ..

/--
@isnad1 id=eq.0h2v.s6.e76c75dccdd3 from=seed src=0 shape=e8ed2977 vocab=aa4cf41c
-/
@[simp]
lemma ψ_one : W.ψ 1 = 1 :=
  normEDS_one ..

/--
@isnad1 id=eq.0h2v.s5.9e7146682caa from=seed src=0 shape=6b074847 vocab=a83f0cb1
-/
@[simp]
lemma ψ_two : W.ψ 2 = W.ψ₂ :=
  normEDS_two ..

/--
@isnad1 id=eq.0h2v.s7.0a6a7767db22 from=seed src=0 shape=36cc48d6 vocab=e8e6a3da
-/
@[simp]
lemma ψ_three : W.ψ 3 = C W.Ψ₃ :=
  normEDS_three ..

/--
@isnad1 id=eq.0h2v.s8.302f69bba255 from=seed src=0 shape=40e7cc17 vocab=70d48fab
-/
@[simp]
lemma ψ_four : W.ψ 4 = C W.preΨ₄ * W.ψ₂ :=
  normEDS_four ..

/--
@isnad1 id=eq.0h3v.s6.7d91d6a50021 from=seed src=0 shape=7604a9b7 vocab=44901cd0
-/
@[simp]
lemma ψ_neg (n : ℤ) : W.ψ (-n) = -W.ψ n :=
  normEDS_neg ..

/--
@isnad1 id=eq.0h3v.s9.fbf7fc278d19 from=seed src=0 shape=025c49c3 vocab=a75034e2
-/
lemma ψ_even (m : ℤ) : W.ψ (2 * m) * W.ψ₂ =
    W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) - W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 :=
  normEDS_even ..

/--
@isnad1 id=eq.0h3v.s9.6d2a04bbbd5f from=seed src=0 shape=c73daf88 vocab=37e24ffd
-/
lemma ψ_odd (m : ℤ) : W.ψ (2 * m + 1) =
    W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3 :=
  normEDS_odd ..

/--
@isnad1 id=eq.0h3v.s8.d493e05cf664 from=seed src=0 shape=e8a9dfd6 vocab=1d647d9c
-/
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]

end ψ

section φ

/-! ### The bivariate polynomials `φₙ` -/

/-- The bivariate polynomials `φₙ`. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

open WeierstrassCurve (Ψ Φ φ)

/--
@isnad1 id=eq.0h2v.s6.6c1729bc8359 from=seed src=0 shape=e8ed2977 vocab=5db5eee8
-/
@[simp]
lemma φ_zero : W.φ 0 = 1 := by
  simp [φ]

/--
@isnad1 id=eq.0h2v.s7.805497078fae from=seed src=0 shape=c8c81d2d vocab=e005cad0
-/
@[simp]
lemma φ_one : W.φ 1 = C X := by
  simp [φ]

/--
@isnad1 id=eq.0h2v.s9.b38e4818bfcd from=seed src=0 shape=b38f3dd3 vocab=dddc8191
-/
@[simp]
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  simp [φ]

/--
@isnad1 id=eq.0h2v.s10.d6674830c9d5 from=seed src=0 shape=6a9ac387 vocab=21c2f4c5
-/
@[simp]
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2 := by
  simp [φ, mul_assoc, sq]

/--
@isnad1 id=eq.0h2v.s10.8c5610833dab from=seed src=0 shape=9b003abe vocab=e9d9aa9b
-/
@[simp]
lemma φ_four :
    W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  rw [φ, ψ_four, show (4 + 1 : ℤ) = 2 * 2 + 1 by rfl, ψ_odd, two_add_two_eq_four, ψ_four,
    show (2 - 1 : ℤ) = 1 by rfl, ψ_two, ψ_one, two_add_one_eq_three, show (4 - 1 : ℤ) = 3 by rfl,
    ψ_three]
  ring1

/--
@isnad1 id=eq.0h3v.s5.cac77173794e from=seed src=0 shape=df4c0555 vocab=01ade243
-/
@[simp]
lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg,
    neg_mul_neg, mul_comm <| W.ψ <| n - 1]

/--
@isnad1 id=eq.0h3v.s9.6a9a2c4f0d58 from=seed src=0 shape=c2b1e79d vocab=9122374b
-/
lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) := by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
    mul_mul_mul_comm _ <| mk W <| ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
    apply_ite C, apply_ite <| mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]

end φ

section Map

/-! ### Maps across ring homomorphisms -/

open WeierstrassCurve (Ψ Φ ψ φ)

variable (f : R →+* S)

/--
@isnad1 id=eq.0h4v.s6.2816e1af5156 from=seed src=0 shape=9a59bd9b vocab=1265bbb4
-/
@[simp]
lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
  simp_rw [ψ₂, Affine.map_polynomialY]

/--
@isnad1 id=eq.0h4v.s6.7282885ce0e6 from=seed src=0 shape=d4bedcf6 vocab=ab2946ee
-/
@[simp]
lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp [Ψ₂Sq, map_ofNat]

/--
@isnad1 id=eq.0h4v.s6.6c5708df0bd1 from=seed src=0 shape=d4bedcf6 vocab=7a30aea5
-/
@[simp]
lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp [Ψ₃]

/--
@isnad1 id=eq.0h4v.s6.e62069fa05a3 from=seed src=0 shape=d4bedcf6 vocab=412563de
-/
@[simp]
lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp [preΨ₄]

/--
@isnad1 id=eq.0h5v.s6.6f1f0bca25e7 from=seed src=0 shape=acb79c08 vocab=cf8f2226
-/
@[simp]
lemma map_preΨ' (n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f := by
  simp [preΨ', ← coe_mapRingHom]

/--
@isnad1 id=eq.0h5v.s6.d1b8c82895d8 from=seed src=0 shape=acb79c08 vocab=3d20cec8
-/
@[simp]
lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f := by
  simp [preΨ, ← coe_mapRingHom]

/--
@isnad1 id=eq.0h5v.s6.5b5d436e92a4 from=seed src=0 shape=acb79c08 vocab=fd6f32ec
-/
@[simp]
lemma map_ΨSq (n : ℤ) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]

/--
@isnad1 id=eq.0h5v.s6.80001cbacfa8 from=seed src=0 shape=0841e15e vocab=f3055673
-/
@[simp]
lemma map_Ψ (n : ℤ) : (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [Ψ, apply_ite <| mapRingHom _]

/--
@isnad1 id=eq.0h5v.s6.b404f4a4b686 from=seed src=0 shape=acb79c08 vocab=cc3b9f4c
-/
@[simp]
lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f := by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]

/--
@isnad1 id=eq.0h5v.s6.b262c64f0348 from=seed src=0 shape=0841e15e vocab=83de4a43
-/
@[simp]
lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [ψ]

/--
@isnad1 id=eq.0h5v.s6.06dd637ec6a9 from=seed src=0 shape=0841e15e vocab=a474f470
-/
@[simp]
lemma map_φ (n : ℤ) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by
  simp [φ]

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

/--
@isnad1 id=eq.0h6v.s8.6f4cfd9f51a8 from=seed src=0 shape=c21b6586 vocab=b8b7406f
-/
lemma baseChange_ψ₂ : (W⁄B).ψ₂ = (W⁄A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.1a0544ee6368 from=seed src=0 shape=f8b5d5ff vocab=6bc1ab9d
-/
lemma baseChange_Ψ₂Sq : (W⁄B).Ψ₂Sq = (W⁄A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.5cecb6ad7a65 from=seed src=0 shape=f8b5d5ff vocab=ce20cbce
-/
lemma baseChange_Ψ₃ : (W⁄B).Ψ₃ = (W⁄A).Ψ₃.map f := by
  rw [← map_Ψ₃, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.8eeab49285f7 from=seed src=0 shape=f8b5d5ff vocab=242579a7
-/
lemma baseChange_preΨ₄ : (W⁄B).preΨ₄ = (W⁄A).preΨ₄.map f := by
  rw [← map_preΨ₄, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.b9e99b55e7f8 from=seed src=0 shape=6c38f422 vocab=ee6a9154
-/
lemma baseChange_preΨ' (n : ℕ) : (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f := by
  rw [← map_preΨ', map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.7c9dbfed9fe9 from=seed src=0 shape=6c38f422 vocab=a2293bb9
-/
lemma baseChange_preΨ (n : ℤ) : (W⁄B).preΨ n = ((W⁄A).preΨ n).map f := by
  rw [← map_preΨ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.67ccb1191efc from=seed src=0 shape=6c38f422 vocab=5d0be846
-/
lemma baseChange_ΨSq (n : ℤ) : (W⁄B).ΨSq n = ((W⁄A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.0618708d20cb from=seed src=0 shape=f4de3c64 vocab=412ee9c9
-/
lemma baseChange_Ψ (n : ℤ) : (W⁄B).Ψ n = ((W⁄A).Ψ n).map (mapRingHom f) := by
  rw [← map_Ψ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.c11ef292be69 from=seed src=0 shape=6c38f422 vocab=c4e65834
-/
lemma baseChange_Φ (n : ℤ) : (W⁄B).Φ n = ((W⁄A).Φ n).map f := by
  rw [← map_Φ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.231b911c76d8 from=seed src=0 shape=f4de3c64 vocab=70b2bd8c
-/
lemma baseChange_ψ (n : ℤ) : (W⁄B).ψ n = ((W⁄A).ψ n).map (mapRingHom f) := by
  rw [← map_ψ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.2a6c46e37f78 from=seed src=0 shape=f4de3c64 vocab=dc393214
-/
lemma baseChange_φ (n : ℤ) : (W⁄B).φ n = ((W⁄A).φ n).map (mapRingHom f) := by
  rw [← map_φ, map_baseChange]

end BaseChange

end WeierstrassCurve
