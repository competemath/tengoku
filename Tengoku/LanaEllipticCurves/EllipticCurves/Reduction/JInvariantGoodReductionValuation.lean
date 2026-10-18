/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantMultiplicativeReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp good-reduction valuation of `j`: `v(j) = v(c₄)³` (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be elliptic (`[W.IsElliptic]`) with good reduction over `R`
(`[HasGoodReduction R W]`). This file records the **good-reduction extreme** of the reduction-type ↔
`v(j)` dictionary (Silverman AEC VII.5.1) at full sharpness, mirroring the merged
multiplicative-reduction identity `valuation_j_of_hasMultiplicativeReduction`
(`v(j) = (v Δ)⁻¹`, `JInvariantReductionType.lean`).

Everything here is fully **ungated**: only the DVR multiplicative-valuation API, the already-merged
factorisation `valuation_j_eq_of_isElliptic` (`v(j) = (v Δ)⁻¹ · (v c₄)³`) and the definitional
`HasGoodReduction.goodReduction` (`v(Δ) = 1`). No valuation-extension, Tate-curve or normality
infrastructure.

## Key point

For good reduction `HasGoodReduction.goodReduction` records exactly `v(Δ) = 1` (the discriminant is
a unit). Feeding this into `v(j) = (v Δ)⁻¹ · (v c₄)³` collapses the discriminant factor and leaves
the sharp `v(j) = (v c₄)³`. This refines `isIntegral_j_of_hasGoodReduction` (which only records
`v(j) ≥ 0`) to an exact value, and — since the value group `ℤᵐ⁰` is a linearly ordered commutative
group with zero on which `x ↦ x³` is strictly monotone, hence injective — yields the classical unit
criterion: under good reduction `j` is a unit exactly when `c₄` is,
i.e. `v(j) = 1 ↔ v(c₄) = 1`.

## Main results

* `WeierstrassCurve.valuation_j_of_hasGoodReduction` — the sharp identity `v(j) = v(c₄)³` under good
  reduction (strengthening `isIntegral_j_of_hasGoodReduction`, which only records `v(j) ≥ 0`).
* `WeierstrassCurve.valuation_j_eq_one_iff_valuation_c₄_eq_one` — the unit criterion
  `v(j) = 1 ↔ v(c₄) = 1`: under good reduction the `j`-invariant is a unit if and only if `c₄` is.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **The valuation of `j` under good reduction is exactly `v(c₄)³`**: since `v(Δ) = 1` for good
reduction, the factorisation `v(j) = (v Δ)⁻¹ · (v c₄)³` collapses to `(v c₄)³`. This sharpens
`isIntegral_j_of_hasGoodReduction` (which only records `v(j) ≥ 0`) and is the good-reduction mirror
of `valuation_j_of_hasMultiplicativeReduction` (`v(j) = (v Δ)⁻¹`). -/
theorem valuation_j_of_hasGoodReduction (W : WeierstrassCurve K)
    [W.IsElliptic] [HasGoodReduction R W] :
    valuation K (maximalIdeal R) W.j = valuation K (maximalIdeal R) W.c₄ ^ 3 := by
  rw [valuation_j_eq_of_isElliptic R W, HasGoodReduction.goodReduction (R := R), inv_one, one_mul]

variable (R) in
/-- **The unit criterion under good reduction**: the `j`-invariant is a unit exactly when `c₄` is,
`v(j) = 1 ↔ v(c₄) = 1`. From `v(j) = v(c₄)³` this is the injectivity of `x ↦ x³` on the value group
`ℤₘ₀` (a linearly ordered commutative group with zero, where every element is `≥ 0`, so cubing is
strictly monotone hence injective on the whole space). -/
theorem valuation_j_eq_one_iff_valuation_c₄_eq_one (W : WeierstrassCurve K)
    [W.IsElliptic] [HasGoodReduction R W] :
    valuation K (maximalIdeal R) W.j = 1 ↔ valuation K (maximalIdeal R) W.c₄ = 1 := by
  rw [valuation_j_of_hasGoodReduction R W]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  exact (pow_left_inj₀ (n := 3) zero_le zero_le (by norm_num)).mp (by rw [h, one_pow])

end WeierstrassCurve
