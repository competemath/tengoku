/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# The addition-and-subtraction map on symmetric `x`-coordinates

Mathlib defines `sym2x P Q`, the symmetric function of the two `x`-coordinates recording the
unordered pair `{P, Q}`, and the quadratic map `addSubMap` that should induce
`{P, Q} ↦ {P + Q, P - Q}` on it. This file proves that it does — up to a nonzero scalar, which
is all a projective statement can assert, and all a scale-invariant height needs.

No height appears here; the consumer is
`TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight`.

## Main results

* `WeierstrassCurve.Affine.Point.sym2x_eq_xRep` : `sym2x` in projective `xRep` coordinates.
* `WeierstrassCurve.Affine.Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x` : there is a
  nonzero `t` with `t • sym2x (P + Q) (P - Q) = addSubMap W ∘ sym2x P Q`.

## Relation to Mathlib

Mathlib's `sym2x`, `addSubMap`, `addSubMapCoeff` and `isHomogeneous_addSubMap` are *consumed*, not
restated. The declarations here are absent from Mathlib at the version this repository pins: the
source brackets this material with a reference to Mathlib PR `#40303`, and
`Mathlib/NumberTheory/Height/EllipticCurve.lean` — by the same author — carries a `TODO` naming
this scope. This is a deliberate, temporary duplication with a defined end: if a later pin bump
lands that upstream work, the superseded declarations here must be deleted and their uses
repointed at Mathlib in the same pull request, per this repository's no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

open MvPolynomial Nat

namespace WeierstrassCurve

namespace Affine

/-! ### `sym2x` and the addition-and-subtraction map -/

section CommRing

variable {F : Type*} [CommRing F] {W : Affine F}

/-- `sym2x` written out in the projective `xRep` coordinates.

Public, and stated rather than unfolded, because Mathlib's `sym2x` is **not exposed**:
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean` opens a plain `public section`, so
across the module boundary the body is unavailable and both `simp [Point.sym2x]` and
`rw [Point.sym2x]` are rejected outright — `Invalid simp theorem \`sym2x\`: Expected a definition
with an exposed body`, and `Invalid rewrite argument`. Mathlib exports only the four
per-constructor `@[simp]` lemmas, so the general equation is recovered here by matching on those
four cases.

It is the *coordinate bridge*, not a competing spelling of `sym2x`: the canonical definition
remains Mathlib's. It is exported rather than kept `private` because the commuting square below
and the height bound in `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight` both
need it, `private` does not cross a module boundary, and the placement review asked for exactly
this ("expose or locally restate only the coordinate bridge needed by the height bound"). -/
lemma Point.sym2x_eq_xRep (P Q : W.Point) :
    P.sym2x Q = ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
      P.xRep 1 * Q.xRep 1] := by
  match P, Q with
  | 0, 0 => simp [Point.xRep_zero]
  | 0, .some x y h => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, 0 => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, .some x' y' h' => simp [Point.xRep_some]

end CommRing

variable {F : Type*} [Field F] {W : Affine F}

section Decidable

variable [DecidableEq F]

end Decidable

end Affine

end WeierstrassCurve

end
