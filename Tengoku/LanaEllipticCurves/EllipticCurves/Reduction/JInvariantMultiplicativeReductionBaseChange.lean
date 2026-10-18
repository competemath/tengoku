/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantMultiplicativeReduction
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicative reduction over a DVR extension makes the `j`-invariant non-integral (issue #72)

Let `L / K` be a field extension and `A : ValuationSubring L` a **discrete** valuation subring of
`L`.  This is the abstract shape of "a finite extension `L / K` with `A` the corresponding valuation
ring", exactly as used by the good-reduction base-change brick
`isIntegral_j_of_hasGoodReduction_baseChange` (`JInvariantGoodReductionBaseChange.lean`, #501).

If a Weierstrass curve `W : WeierstrassCurve K` (elliptic) base changes to a curve `W⁄L` with
**multiplicative reduction over `A`**, then its `j`-invariant `W.j ∈ K` is **not integral at the
base place**: its image `algebraMap K L W.j` lies *outside* `A`, equivalently `W.j` lies outside the
contracted valuation ring `A.comap (algebraMap K L)` of `K`.

This is the **multiplicative-reduction companion** of the good-reduction base-change brick #501
(good reduction ⟹ `j ∈ A`) and the base-landing #504 (potential good reduction ⟹ `j` integral): it
is the *potential multiplicative reduction* obstruction — the base-change reflection of
`not_isIntegral_j_of_hasMultiplicativeReduction` (`JInvariantMultiplicativeReduction.lean`), the
easy direction of Silverman AEC VII.5.1 ("multiplicative reduction is detected by `v(j) < 0`").  As
in
#501 the "`A` lies over the base" condition is free: `ValuationSubring.comap` and
`ValuationSubring.mem_comap` give `x ∈ A.comap f ↔ f x ∈ A`, so no ad-hoc `A ∩ K = R` hypothesis or
ramification-index machinery is needed.

## Main results

* `WeierstrassCurve.not_mem_j_of_hasMultiplicativeReduction_baseChange` — multiplicative reduction
  of `W⁄L` over `A` implies `algebraMap K L W.j ∉ A`.
* `WeierstrassCurve.not_mem_comap_j_of_hasMultiplicativeReduction_baseChange` — the same, phrased as
  `W.j ∉ A.comap (algebraMap K L)` (the `j`-invariant is *not* integral at the contracted place of
  `K`).
* `WeierstrassCurve.not_hasMultiplicativeReduction_baseChange_of_j_mem` — the contrapositive: a
  `j`-invariant that *is* integral at the base place rules out multiplicative reduction over `A`.

## Scope

This delivers the reusable *per-extension* core of the multiplicative obstruction.  The full
statement quantifies over all finite extensions `L / K`, and the *converse* (`v(j) < 0` ⟹
*potential* multiplicative reduction, the Tate curve) needs infrastructure absent from the
repository and the pinned Mathlib; both remain larger efforts.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1, VII.5.5.
-/

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Multiplicative reduction over a DVR extension forces `j` non-integral at the base.** If the
base change `W⁄L` has multiplicative reduction over the discrete valuation subring `A ⊆ L`, then the
image of the `j`-invariant `algebraMap K L W.j` lies *outside* `A`. This is the base-change
reflection of `not_isIntegral_j_of_hasMultiplicativeReduction` — the multiplicative-reduction
companion of `isIntegral_j_of_hasGoodReduction_baseChange` (#501). -/
theorem not_mem_j_of_hasMultiplicativeReduction_baseChange
    (h : HasMultiplicativeReduction A (W⁄L)) : algebraMap K L W.j ∉ A := by
  haveI : HasMultiplicativeReduction A (W⁄L) := h
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  intro hmem
  refine not_isIntegral_j_of_hasMultiplicativeReduction A (W⁄L) ⟨⟨algebraMap K L W.j, hmem⟩, ?_⟩
  rw [ValuationSubring.algebraMap_apply,
    show (W⁄L).j = algebraMap K L W.j from W.map_j (algebraMap K L)]

/-- **The `j`-invariant is not integral at the contracted place.** Restatement of
`not_mem_j_of_hasMultiplicativeReduction_baseChange` as non-membership in the contracted valuation
ring `A.comap (algebraMap K L)` of `K`. -/
theorem not_mem_comap_j_of_hasMultiplicativeReduction_baseChange
    (h : HasMultiplicativeReduction A (W⁄L)) : W.j ∉ A.comap (algebraMap K L) :=
  fun hmem => not_mem_j_of_hasMultiplicativeReduction_baseChange A W h
    (ValuationSubring.mem_comap.mp hmem)

/-- **A `j`-invariant that is integral at the base place rules out multiplicative reduction over
`A`.** Contrapositive of `not_mem_j_of_hasMultiplicativeReduction_baseChange`: if
`algebraMap K L W.j ∈ A`, then the base change `W⁄L` cannot have multiplicative reduction over
`A`. -/
theorem not_hasMultiplicativeReduction_baseChange_of_j_mem
    (h : algebraMap K L W.j ∈ A) : ¬ HasMultiplicativeReduction A (W⁄L) :=
  fun hmult => not_mem_j_of_hasMultiplicativeReduction_baseChange A W hmult h

end WeierstrassCurve
