/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantMultiplicativeReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reduction-type ↔ `v(j)` dictionary: sharp pole order and bad reduction (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K`. This file completes the elementary consequences of the reduction-type ↔
`v(j)` dictionary (Silverman AEC VII.5.1) whose two extremes are already recorded:

* good reduction ⇒ integral `j`
  (`isIntegral_j_of_hasGoodReduction`, `JInvariantGoodReduction.lean`);
* multiplicative reduction ⇒ non-integral `j`
  (`not_isIntegral_j_of_hasMultiplicativeReduction`, `JInvariantMultiplicativeReduction.lean`).

Everything here is a short consequence of those merged bricks plus Mathlib's reduction-type
trichotomy, and is fully **ungated** (only the DVR valuation API; no valuation-extension,
Tate-curve or normality infrastructure).

## Key point

For multiplicative reduction the valuation of `j` is not merely negative but is pinned exactly:
from `v(j) = (v Δ)⁻¹ · (v c₄)³` (`valuation_j_eq_of_isElliptic`) and `v(c₄) = 1`
(`HasMultiplicativeReduction.multiplicativeReduction`) it collapses to `v(j) = (v Δ)⁻¹`, i.e. the
order of the pole of `j` equals `v(Δ)` — the classical fact `v(j) = -v(Δ)`.
Dually, the good-reduction brick contrapositive says a non-integral `j` rules out good reduction, so
on a minimal model a non-integral `j` forces **bad** reduction (multiplicative or additive).

## Main results

* `WeierstrassCurve.valuation_j_of_hasMultiplicativeReduction` — the sharp identity
  `valuation K (maximalIdeal R) W.j = (valuation K (maximalIdeal R) W.Δ)⁻¹` under multiplicative
  reduction (strengthening `one_lt_valuation_j_of_hasMultiplicativeReduction`, which only
  records the sign).
* `WeierstrassCurve.not_hasGoodReduction_of_not_isIntegral_j` — a non-integral `j`-invariant rules
  out good reduction (contrapositive of `isIntegral_j_of_hasGoodReduction`).
* `WeierstrassCurve.hasMultiplicativeReduction_or_hasAdditiveReduction_of_not_isIntegral_j` — on a
  minimal model, a non-integral `j`-invariant forces bad reduction:
  `HasMultiplicativeReduction R W ∨ HasAdditiveReduction R W`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **The pole order of `j` under multiplicative reduction is `v(Δ)`**: the valuation of the
`j`-invariant is exactly `(v Δ)⁻¹`. This sharpens
`one_lt_valuation_j_of_hasMultiplicativeReduction` (which only records `1 < v(j)`, i.e. the sign),
and is the classical `v(j) = -v(Δ)`. Since `v(c₄) = 1` for multiplicative reduction, the identity
`v(j) = (v Δ)⁻¹ · (v c₄)³` collapses to `(v Δ)⁻¹`. -/
theorem valuation_j_of_hasMultiplicativeReduction (W : WeierstrassCurve K)
    [W.IsElliptic] [HasMultiplicativeReduction R W] :
    valuation K (maximalIdeal R) W.j = (valuation K (maximalIdeal R) W.Δ)⁻¹ := by
  rw [valuation_j_eq_of_isElliptic R W,
    HasMultiplicativeReduction.multiplicativeReduction (R := R), one_pow, mul_one]

variable (R) in
/-- **A non-integral `j`-invariant rules out good reduction**: if there is no `r : R` with
`algebraMap R K r = W.j`, then `W` does not have good reduction over `R`. This is the contrapositive
of `isIntegral_j_of_hasGoodReduction` (good reduction ⇒ `j` integral). -/
theorem not_hasGoodReduction_of_not_isIntegral_j (W : WeierstrassCurve K) [W.IsElliptic]
    (h : ¬ ∃ r : R, algebraMap R K r = W.j) : ¬ W.HasGoodReduction R := by
  intro hgr
  letI : W.HasGoodReduction R := hgr
  exact h (isIntegral_j_of_hasGoodReduction R W)

variable (R) in
/-- **A non-integral `j`-invariant forces bad reduction**: for a minimal model whose
`j`-invariant is not integral (no `r : R` with `algebraMap R K r = W.j`), the reduction is bad —
multiplicative or additive. Good reduction is excluded by
`not_hasGoodReduction_of_not_isIntegral_j`, so the reduction-type trichotomy leaves exactly the two
bad cases. -/
theorem hasMultiplicativeReduction_or_hasAdditiveReduction_of_not_isIntegral_j
    (W : WeierstrassCurve K) [W.IsElliptic] [IsMinimal R W]
    (h : ¬ ∃ r : R, algebraMap R K r = W.j) :
    W.HasMultiplicativeReduction R ∨ W.HasAdditiveReduction R := by
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R) (W := W)
    with hg | hm | ha
  · exact absurd hg (not_hasGoodReduction_of_not_isIntegral_j R W h)
  · exact Or.inl hm
  · exact Or.inr ha

end WeierstrassCurve
