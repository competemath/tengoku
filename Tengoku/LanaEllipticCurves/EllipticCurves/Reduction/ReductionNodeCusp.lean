/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionInvariants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Node vs cusp: bad reduction classified by the reduced curve's invariants (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  Mathlib
defines the three reduction types of the minimal model by the valuations of `Δ` and `c₄`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`):

* good reduction: `v(Δ) = 1` (a unit);
* multiplicative reduction: `v(Δ) < 1` and `v(c₄) = 1`;
* additive reduction: `v(Δ) < 1` and `v(c₄) < 1`.

This file translates that valuation-level dictionary into the **reduced curve's own invariants**.
Since `v(x) < 1 ⟺ x` lies in the maximal ideal `⟺ residue R x = 0`, and reduction commutes with the
invariants (`reduction_Δ_eq`, `reduction_c₄_eq`, #490), the reduction type is read off directly from
whether the discriminant `Δ̃` and the invariant `c̃₄` of the reduced curve `W.reduction R` over the
residue field vanish:

* **good** ⟺ `Δ̃ ≠ 0` (the reduced curve is smooth / elliptic — this is Mathlib's
  `hasGoodReduction_iff_isElliptic_reduction`, restated here as `Δ̃ ≠ 0`);
* **multiplicative** ⟺ `Δ̃ = 0 ∧ c̃₄ ≠ 0` (a **node**);
* **additive** ⟺ `Δ̃ = 0 ∧ c̃₄ = 0` (a **cusp**).

This is the reduced-curve-geometry face of the reduction-type trichotomy — the natural sibling
of the invariant dictionary (#490) and of `hasGoodReduction_iff_isElliptic_reduction`.  It is
fully unconditional (only `IsMinimal R W`) and needs no Tate-curve / valuation-extension theory.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]`, in `namespace WeierstrassCurve`:

* `reduction_Δ_eq_zero_iff` — `(W.reduction R).Δ = 0 ↔ v(Δ) < 1` (the bad-reduction bridge);
* `reduction_c₄_eq_zero_iff` — `(W.reduction R).c₄ = 0 ↔ v(c₄) < 1`;
* `hasGoodReduction_iff_reduction_Δ_ne_zero` — good reduction ⟺ `(W.reduction R).Δ ≠ 0`;
* `hasMultiplicativeReduction_iff_reduction` — multiplicative reduction ⟺
  `(W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ ≠ 0` (node);
* `hasAdditiveReduction_iff_reduction` — additive reduction ⟺
  `(W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ = 0` (cusp).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **The discriminant of the reduced curve vanishes iff the discriminant has positive valuation.**
`(W.reduction R).Δ = 0` (the reduced curve is singular) exactly when `v(Δ) < 1`, i.e. `W` does not
have good reduction. -/
theorem reduction_Δ_eq_zero_iff (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).Δ = 0 ↔ valuation K (maximalIdeal R) W.Δ < 1 := by
  rw [reduction_Δ_eq R W, residue_eq_zero_iff, ← integralModel_Δ_eq R W]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (integralModel R W).Δ).symm

variable (R) in
/-- **The `c₄`-invariant of the reduced curve vanishes iff `c₄` has positive valuation.**
`(W.reduction R).c₄ = 0` exactly when `v(c₄) < 1`. -/
theorem reduction_c₄_eq_zero_iff (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).c₄ = 0 ↔ valuation K (maximalIdeal R) W.c₄ < 1 := by
  rw [reduction_c₄_eq R W, residue_eq_zero_iff, ← integralModel_c₄_eq R W]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (integralModel R W).c₄).symm

variable (R) in
/-- Under a minimal model, `v(c₄) ≤ 1`: `c₄` is integral, so its valuation is at most `1`. -/
theorem valuation_c₄_le_one (W : WeierstrassCurve K) [IsMinimal R W] :
    valuation K (maximalIdeal R) W.c₄ ≤ 1 := by
  rw [← integralModel_c₄_eq R W]; exact valuation_le_one (maximalIdeal R) _

variable (R) in
/-- **Good reduction is detected by the reduced discriminant.** `W` has good reduction iff the
discriminant of the reduced curve is nonzero (equivalently, the reduced curve is elliptic).  This is
`hasGoodReduction_iff_isElliptic_reduction` phrased through `Δ̃ ≠ 0`. -/
theorem hasGoodReduction_iff_reduction_Δ_ne_zero (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasGoodReduction R ↔ (W.reduction R).Δ ≠ 0 := by
  rw [hasGoodReduction_iff_isElliptic_reduction, isElliptic_iff, isUnit_iff_ne_zero]

variable (R) in
/-- **Multiplicative reduction is a node.** For a minimal model, `W` has multiplicative reduction
iff the reduced curve is singular (`Δ̃ = 0`) with a nonvanishing `c₄`-invariant (`c̃₄ ≠ 0`) — the
invariant-theoretic signature of a node. -/
theorem hasMultiplicativeReduction_iff_reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasMultiplicativeReduction R ↔ (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ ≠ 0 := by
  constructor
  · intro h
    refine ⟨(reduction_Δ_eq_zero_iff R W).2 h.badReduction, ?_⟩
    rw [Ne, reduction_c₄_eq_zero_iff R W, h.multiplicativeReduction]
    exact lt_irrefl 1
  · rintro ⟨hΔ, hc₄⟩
    refine { badReduction := (reduction_Δ_eq_zero_iff R W).1 hΔ, multiplicativeReduction := ?_ }
    refine le_antisymm (valuation_c₄_le_one R W) (not_lt.1 fun hlt => hc₄ ?_)
    exact (reduction_c₄_eq_zero_iff R W).2 hlt

variable (R) in
/-- **Additive reduction is a cusp.** For a minimal model, `W` has additive reduction iff the
reduced curve is singular (`Δ̃ = 0`) with a vanishing `c₄`-invariant (`c̃₄ = 0`) — the
invariant-theoretic signature of a cusp. -/
theorem hasAdditiveReduction_iff_reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasAdditiveReduction R ↔ (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ = 0 := by
  constructor
  · intro h
    exact ⟨(reduction_Δ_eq_zero_iff R W).2 h.badReduction,
      (reduction_c₄_eq_zero_iff R W).2 h.additiveReduction⟩
  · rintro ⟨hΔ, hc₄⟩
    refine { badReduction := (reduction_Δ_eq_zero_iff R W).1 hΔ, additiveReduction := ?_ }
    exact (reduction_c₄_eq_zero_iff R W).1 hc₄

end WeierstrassCurve
