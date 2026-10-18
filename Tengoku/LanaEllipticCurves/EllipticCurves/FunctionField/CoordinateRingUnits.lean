/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Units of the affine coordinate ring are the nonzero constants

Let `W` be a Weierstrass curve over a field `F`.  Its affine coordinate ring
`F[W] = WeierstrassCurve.Affine.CoordinateRing` is a rank-two free `F[X]`-module with basis
`{1, Y}`, so every element is `p • 1 + q • Y` for `p q : F[X]`, and there is an algebra norm
`N : F[W] → F[X]` whose degree is `max (2 · deg p) (2 · deg q + 3)` (Mathlib's
`degree_norm_smul_basis`).

Geometrically `F[W]` is the ring of functions regular away from the point at infinity, so a unit —
regular and non-vanishing on the affine chart, with a regular non-vanishing inverse — has empty
divisor and must be a constant.  This file proves that arithmetically from the degree formula:

* `WeierstrassCurve.Affine.CoordinateRing.exists_eq_algebraMap_of_isUnit` — every unit of `F[W]`
  is `algebraMap F F[W] c` for some `c : F`;
* `WeierstrassCurve.Affine.CoordinateRing.isUnit_iff_exists_eq_algebraMap` — the characterisation
  `IsUnit x ↔ ∃ c : F, c ≠ 0 ∧ x = algebraMap F F[W] c`.

If `x` is a unit then `N x` is a unit of `F[X]`, hence a nonzero constant, so `deg (N x) = 0`.
Writing `x = p • 1 + q • Y`, the degree formula reads `max (2 · deg p) (2 · deg q + 3) = 0`, which
forces `q = 0` (else the second term is `≥ 3`) and `deg p = 0`, i.e. `x = C c` for a nonzero
constant `c`.

This is **Ward- and normality-independent**: it uses only the free-module / norm structure of
`F[W]` over `F[X]`, needing just `[Field F]` (no `IsDedekindDomain`, no elliptic-net input, not even
`W.IsElliptic`).  It supplies the "the unit `u` is a constant" input (`huf`) of the
divisor-theoretic Weil-pairing element (issue #419).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2, III.3.
-/

open Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **The units of `F[W]` are the nonzero constants.**  Every unit `x` of the affine coordinate ring
is the image `algebraMap F F[W] c` of a scalar `c : F`.

The norm `N x ∈ F[X]` of a unit is a unit of `F[X]`, hence a nonzero constant with
`deg (N x) = 0`.  Writing `x = p • 1 + q • Y`, the degree formula
`deg (N x) = max (2 • deg p) (2 • deg q + 3)` (`degree_norm_smul_basis`) forces `q = 0` and
`deg p = 0`, so `x = C (p.coeff 0)` is a constant. -/
theorem exists_eq_algebraMap_of_isUnit {x : W.CoordinateRing} (hx : IsUnit x) :
    ∃ c : F, x = algebraMap F W.CoordinateRing c := by
  -- The norm to `F[X]` of a unit is a unit of `F[X]`, hence has degree `0`.
  have hnu : IsUnit (Algebra.norm F[X] x) := hx.map (Algebra.norm F[X])
  have hdeg0 : (Algebra.norm F[X] x).degree = 0 := isUnit_iff_degree_eq_zero.mp hnu
  -- Write `x = p • 1 + q • Y` and read off the degree formula.
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq x
  rw [degree_norm_smul_basis] at hdeg0
  -- `max (2 • deg p) (2 • deg q + 3) = 0`.
  have hq3 : 2 • q.degree + 3 ≤ (0 : WithBot ℕ) := (le_max_right _ _).trans hdeg0.le
  -- The `q`-term is `≥ 3` unless `q = 0`, so `q = 0`.
  have hq0 : q = 0 := by
    by_contra hq
    have hqd : (0 : WithBot ℕ) ≤ q.degree := zero_le_degree_iff.mpr hq
    have h2q : (0 : WithBot ℕ) ≤ 2 • q.degree := by
      rw [two_nsmul]; exact add_nonneg hqd hqd
    have : (3 : WithBot ℕ) ≤ 2 • q.degree + 3 := le_add_of_nonneg_left h2q
    exact absurd (this.trans hq3) (by decide)
  -- With `q = 0` the formula collapses to `2 • deg p = 0`, so `deg p = 0`.
  subst hq0
  simp only [degree_zero, two_nsmul, WithBot.bot_add, max_bot_right] at hdeg0
  -- `hdeg0 : p.degree + p.degree = 0`, so `p.degree = 0`.
  have hp0 : p.degree = 0 := (Nat.WithBot.add_eq_zero_iff.mp hdeg0).1
  -- `p` is the constant `C (p.coeff 0)`; assemble the witness.
  refine ⟨p.coeff 0, ?_⟩
  have hp : p = C (p.coeff 0) := eq_C_of_degree_eq_zero hp0
  rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, ← Polynomial.C_eq_algebraMap, ← hp]

/-- **Unit characterisation of `F[W]`.**  An element `x` of the affine coordinate ring is a unit iff
it is `algebraMap F F[W] c` for a nonzero constant `c : F`. -/
theorem isUnit_iff_exists_eq_algebraMap {x : W.CoordinateRing} :
    IsUnit x ↔ ∃ c : F, c ≠ 0 ∧ x = algebraMap F W.CoordinateRing c := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_isUnit hx
    refine ⟨c, ?_, rfl⟩
    rintro rfl
    rw [map_zero] at hx
    exact not_isUnit_zero hx
  · rintro ⟨c, hc, rfl⟩
    exact (Ne.isUnit hc).map (algebraMap F W.CoordinateRing)

end WeierstrassCurve.Affine.CoordinateRing
