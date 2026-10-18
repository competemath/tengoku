/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantGoodReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicative reduction makes the `j`-invariant non-integral (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be elliptic (`[W.IsElliptic]`). This file records the
**multiplicative-reduction half** of the reduction-type ↔ `v(j)` dictionary (Silverman AEC
VII.5.1): a curve with multiplicative reduction has a **non-integral** `j`-invariant,
`v(j) < 0`. This is the opposite extreme to the good-reduction brick
`isIntegral_j_of_hasGoodReduction` (`JInvariantGoodReduction.lean`, #483), which shows good
reduction forces `v(j) ≥ 0`.

## Key point

Writing `j = Δ'⁻¹ · c₄³` and pushing through the (multiplicative) valuation `valuation K
(maximalIdeal R)` gives `v(j) = (v Δ)⁻¹ · (v c₄)³`. For multiplicative reduction Mathlib's
`HasMultiplicativeReduction` records exactly `v(c₄) = 1` (a unit) and `v(Δ) < 1` (positive
additive valuation). Since `[W.IsElliptic]` makes `Δ` a unit, hence nonzero, `v Δ ≠ 0`, so
`v(j) = (v Δ)⁻¹ > 1` — i.e. `j` lies outside `R`. This is the easy direction of the classical
statement that multiplicative reduction is detected by `v(j) < 0`; the converse (`v(j) < 0`
implies *potential* multiplicative reduction, the Tate curve) needs infrastructure absent from
both the repository and Mathlib and is left to a follow-on.

## Main results

* `WeierstrassCurve.valuation_j_eq_of_isElliptic` — the valuation identity
  `v(j) = (v Δ)⁻¹ · (v c₄)³` for any elliptic `W`.
* `WeierstrassCurve.one_lt_valuation_j_of_hasMultiplicativeReduction` — multiplicative reduction
  implies `1 < v(j)` (multiplicative-valuation convention for `v(j) < 0`).
* `WeierstrassCurve.not_isIntegral_j_of_hasMultiplicativeReduction` — the `j`-invariant of a curve
  with multiplicative reduction is **not** integral: `¬ ∃ r : R, algebraMap R K r = W.j`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- The valuation of the `j`-invariant of an elliptic curve factors as `(v Δ)⁻¹ · (v c₄)³`, since
`j = Δ'⁻¹ · c₄³` and the valuation is multiplicative. -/
theorem valuation_j_eq_of_isElliptic (W : WeierstrassCurve K) [W.IsElliptic] :
    valuation K (maximalIdeal R) W.j
      = (valuation K (maximalIdeal R) W.Δ)⁻¹ * valuation K (maximalIdeal R) W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, map_mul, map_pow, Units.val_inv_eq_inv_val, coe_Δ', map_inv₀]

variable (R) in
/-- **Multiplicative reduction forces `v(j) < 0`** (here `1 < v(j)` in the multiplicative valuation
convention): with `v(c₄) = 1` and `0 < v(Δ) < 1`, the identity `v(j) = (v Δ)⁻¹ · (v c₄)³`
collapses to `v(j) = (v Δ)⁻¹ > 1`. -/
theorem one_lt_valuation_j_of_hasMultiplicativeReduction (W : WeierstrassCurve K)
    [W.IsElliptic] [HasMultiplicativeReduction R W] :
    1 < valuation K (maximalIdeal R) W.j := by
  have hΔ : valuation K (maximalIdeal R) W.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).2 W.Δ'.ne_zero
  rw [valuation_j_eq_of_isElliptic R W, HasMultiplicativeReduction.multiplicativeReduction (R := R),
    one_pow, mul_one, one_lt_inv₀ (pos_iff_ne_zero.2 hΔ)]
  exact HasMultiplicativeReduction.badReduction

variable (R) in
/-- **The `j`-invariant of a curve with multiplicative reduction is not integral**: there is no
`r : R` with `algebraMap R K r = W.j`. Contrast `isIntegral_j_of_hasGoodReduction` (#483). -/
theorem not_isIntegral_j_of_hasMultiplicativeReduction (W : WeierstrassCurve K)
    [W.IsElliptic] [HasMultiplicativeReduction R W] :
    ¬ ∃ r : R, algebraMap R K r = W.j := by
  rintro ⟨r, hr⟩
  have h := one_lt_valuation_j_of_hasMultiplicativeReduction R W
  rw [← hr] at h
  exact absurd (valuation_le_one (maximalIdeal R) r) (not_le.2 h)

end WeierstrassCurve
