/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantGoodReduction
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Good reduction over a DVR extension forces the `j`-invariant integral at the base (issue #501)

Let `L / K` be a field extension and `A : ValuationSubring L` a **discrete** valuation subring of
`L`.  This is the abstract shape of "a finite extension `L / K` with `A` the corresponding valuation
ring", exactly as used by the Néron–Ogg–Shafarevich *good ⇒ unramified* tree
(`EllipticCurves/Reduction/ReductionUnramified.lean`, with `A.inertiaSubgroup K`).

If a Weierstrass curve `W : WeierstrassCurve K` (elliptic) base changes to a curve `W⁄L` with
**good reduction over `A`**, then its `j`-invariant `W.j ∈ K` is **integral at the base place**: its
image lies in `A`, equivalently `W.j` lies in the contracted valuation ring
`A.comap (algebraMap K L)` of `K`.

This is the **base-change reflection** of the merged good-reduction ⇒ integral-`j` brick
`WeierstrassCurve.isIntegral_j_of_hasGoodReduction` (`JInvariantGoodReduction.lean`, issue #483):
the *ungated* direction of Silverman AEC VII.5.5 — "(potential) good reduction ⟹ `j` integral".
The key point is that the "`A` lies over the base" condition is free: `ValuationSubring.comap` and
`ValuationSubring.mem_comap` give `x ∈ A.comap f ↔ f x ∈ A`, so no ad-hoc `A ∩ K = R` hypothesis or
ramification-index machinery is needed.

## Main results

* `WeierstrassCurve.isIntegral_j_of_hasGoodReduction_baseChange` — good reduction of `W⁄L` over `A`
  implies `algebraMap K L W.j ∈ A`.
* `WeierstrassCurve.mem_comap_j_of_hasGoodReduction_baseChange` — the same, phrased as
  `W.j ∈ A.comap (algebraMap K L)` (the `j`-invariant is integral at the contracted place of `K`).
* `WeierstrassCurve.not_hasGoodReduction_baseChange_of_j_not_mem` — the contrapositive: a
  `j`-invariant that is not integral at the base place rules out good reduction over `A`.

## Scope

This delivers the reusable *per-extension* core.  The full VII.5.5 statement quantifies over all
finite extensions `L / K` (a `PotentialGoodReduction` predicate, absent from the repo), and its
*converse* (`j` integral ⟹ potential good reduction) needs Tate-curve / valuation-extension
existence infrastructure absent from the repo and the pinned Mathlib; both remain larger efforts.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.5, VII.5.4.
-/

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Good reduction over a DVR extension forces `j` integral at the base.** If the base change
`W⁄L` has good reduction over the discrete valuation subring `A ⊆ L`, then the image of the
`j`-invariant `algebraMap K L W.j` lies in `A`. This is the base-change reflection of
`isIntegral_j_of_hasGoodReduction` (#483) — the ungated direction of Silverman AEC VII.5.5. -/
theorem isIntegral_j_of_hasGoodReduction_baseChange
    (h : HasGoodReduction A (W⁄L)) : algebraMap K L W.j ∈ A := by
  haveI : HasGoodReduction A (W⁄L) := h
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  obtain ⟨a, ha⟩ := isIntegral_j_of_hasGoodReduction A (W⁄L)
  -- `(W⁄L).j = algebraMap K L W.j`, and `algebraMap A L a = ↑a ∈ A`.
  rw [show (W⁄L).j = algebraMap K L W.j from W.map_j (algebraMap K L)] at ha
  rw [← ha, ValuationSubring.algebraMap_apply]
  exact a.2

/-- **The `j`-invariant is integral at the contracted place.** Restatement of
`isIntegral_j_of_hasGoodReduction_baseChange` as membership in the contracted valuation ring
`A.comap (algebraMap K L)` of `K`. -/
theorem mem_comap_j_of_hasGoodReduction_baseChange
    (h : HasGoodReduction A (W⁄L)) : W.j ∈ A.comap (algebraMap K L) :=
  ValuationSubring.mem_comap.mpr (isIntegral_j_of_hasGoodReduction_baseChange A W h)

/-- **A `j`-invariant that is not integral at the base place rules out good reduction over `A`.**
Contrapositive of `isIntegral_j_of_hasGoodReduction_baseChange`: if `algebraMap K L W.j ∉ A`, then
the base change `W⁄L` cannot have good reduction over `A`. -/
theorem not_hasGoodReduction_baseChange_of_j_not_mem
    (h : algebraMap K L W.j ∉ A) : ¬ HasGoodReduction A (W⁄L) :=
  fun hgood => h (isIntegral_j_of_hasGoodReduction_baseChange A W hgood)

end WeierstrassCurve
