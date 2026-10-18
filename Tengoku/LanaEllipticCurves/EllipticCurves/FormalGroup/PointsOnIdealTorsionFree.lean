/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PointsOnIdealTorsion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Ê(𝔪)` is torsion-free in characteristic `0`

Let `A` be a `ℚ`-algebra that is `I`-adically complete (`IsAdicComplete I A`) and let
`F : FormalGroup A`.  The ideal `I` carries the abelian group `Ê(𝔪) = F.OnIdeal I`
(`PointsOnIdeal`).  The merged `PointsOnIdealTorsion` proves that multiplication-by-`m` is bijective
whenever `(m : A)` is a unit — the *prime-to-`p`* torsion story (Silverman AEC IV.3.2(b), VII.2.2).

Over a `ℚ`-algebra **every** nonzero natural number is invertible, so that hypothesis is automatic
and `Ê(𝔪)` is torsion-free outright.  This is the char-0 statement Silverman AEC IV.6.1 records via
the formal-logarithm isomorphism `Ê(𝔪) ≅ 𝔾ₐ`.  We package it as the Mathlib typeclass
`IsAddTorsionFree`, which then equips `Ê(𝔪)` with `NoZeroSMulDivisors ℕ`/`ℤ` and the whole
`zsmul_eq_zero_iff` API for free.

## Main results

* `FormalGroup.OnIdeal.instIsAddTorsionFree` — `IsAddTorsionFree (OnIdeal F I)` over a `ℚ`-algebra.
* `FormalGroup.OnIdeal.eq_zero_of_nsmul_eq_zero_of_ne_zero` — `m ≠ 0 → m • x = 0 → x = 0` (`ℕ`).
* `FormalGroup.OnIdeal.eq_zero_of_zsmul_eq_zero` — `n ≠ 0 → n • x = 0 → x = 0` (`ℤ`).
* `FormalGroup.OnIdeal.nsmul_bijective_of_ne_zero` — char-0 unique `m`-divisibility.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.1 (torsion-freeness in char 0), IV.3.2(b),
VII.2.2 (the prime-to-`p` case).
-/

noncomputable section

namespace FormalGroup

variable {A : Type*} [CommRing A] [Algebra ℚ A] {F : FormalGroup A} {I : Ideal A}
  [IsAdicComplete I A]

namespace OnIdeal

/-- In a `ℚ`-algebra every nonzero natural number is a unit: `(m : A) = algebraMap ℚ A (m : ℚ)` and
`(m : ℚ) ≠ 0` is a unit of the field `ℚ`. -/
private theorem isUnit_natCast {m : ℕ} (hm : m ≠ 0) : IsUnit (m : A) := by
  simpa using (Nat.cast_ne_zero.mpr hm : (m : ℚ) ≠ 0).isUnit.map (algebraMap ℚ A)

/-- **`Ê(𝔪)` is torsion-free in characteristic `0`.**  Over a `ℚ`-algebra, multiplication by every
nonzero `m : ℕ` is injective on `Ê(𝔪)` (Silverman AEC IV.6.1); this is the merged unit-hypothesis
injectivity `nsmul_injective` with `IsUnit (m : A)` supplied automatically.  Yields
`NoZeroSMulDivisors ℕ`/`ℤ (OnIdeal F I)` by the Mathlib instances. -/
instance instIsAddTorsionFree : IsAddTorsionFree (OnIdeal F I) where
  nsmul_right_injective _ hm := nsmul_injective (isUnit_natCast hm)

/-- **No `ℕ`-torsion in char 0.**  Over a `ℚ`-algebra, `m • x = 0` with `m ≠ 0` forces `x = 0`. -/
theorem eq_zero_of_nsmul_eq_zero_of_ne_zero {m : ℕ} (hm : m ≠ 0) {x : OnIdeal F I}
    (h : m • x = 0) : x = 0 :=
  eq_zero_of_nsmul_eq_zero (isUnit_natCast hm) h

/-- **No `ℤ`-torsion in char 0.**  Over a `ℚ`-algebra, `n • x = 0` with `n ≠ 0` forces `x = 0`. -/
theorem eq_zero_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x : OnIdeal F I}
    (h : n • x = 0) : x = 0 :=
  (IsAddTorsionFree.zsmul_eq_zero_iff_right hn).mp h

/-- **Unique `m`-divisibility of `Ê(𝔪)` in char 0.**  Over a `ℚ`-algebra, multiplication by every
nonzero `m : ℕ` is bijective (the char-0 case of `nsmul_bijective`). -/
theorem nsmul_bijective_of_ne_zero {m : ℕ} (hm : m ≠ 0) :
    Function.Bijective (fun x : OnIdeal F I => m • x) :=
  nsmul_bijective (isUnit_natCast hm)

end OnIdeal

end FormalGroup

end
