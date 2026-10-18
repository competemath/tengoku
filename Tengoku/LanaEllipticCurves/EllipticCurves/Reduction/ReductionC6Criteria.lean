/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionC6Signature

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `c₆`-only node/cusp criteria for bad reduction (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  The
node/cusp dictionary of `ReductionNodeCusp.lean` (#490/#491) reads the bad-reduction type off the
reduced curve's discriminant `Δ̃` and `c₄`-invariant `c̃₄`, and `ReductionC6Signature.lean` (#495)
supplies the matching `c₆` *implications* — a node has `c̃₆ ≠ 0`, a cusp has `c̃₆ = 0`.  What was
still missing is the clean `c₆`-only **iff** characterizations, the exact mirror of
`ReductionNodeCusp`'s c₄-only `hasMultiplicativeReduction_iff_reduction` /
`hasAdditiveReduction_iff_reduction`.

This file closes that gap.  The key algebraic fact is that among bad reduction (`Δ̃ = 0`) the
invariants `c̃₄` and `c̃₆` vanish together: Mathlib's invariant relation
`c_relation : 1728 · Δ = c₄³ − c₆²`, applied to the reduced curve where `Δ̃ = 0`, gives
`c̃₄³ = c̃₆²`, so in the field `ResidueField R` one is zero iff the other is.  Hence detecting
the node/cusp split
by `c̃₆` is equivalent to detecting it by `c̃₄`:

* **multiplicative** (a **node**) ⟺ `Δ̃ = 0 ∧ c̃₆ ≠ 0`;
* **additive** (a **cusp**) ⟺ `Δ̃ = 0 ∧ c̃₆ = 0`.

Like its `c₄` sibling this is pure residue-field algebra: it uses only `1728 · 0 = 0`, holds in
**every** characteristic, and is fully unconditional (only `IsMinimal R W`) — no Tate-curve,
valuation-extension, or Néron-model theory.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]`, in `namespace WeierstrassCurve`:

* `reduction_c₄_eq_zero_iff_c₆_eq_zero` — among bad reduction (`Δ̃ = 0`), `c̃₄ = 0 ↔ c̃₆ = 0`;
* `hasMultiplicativeReduction_iff_reduction_c₆` — multiplicative reduction ⟺ `Δ̃ = 0 ∧ c̃₆ ≠ 0`
  (node);
* `hasAdditiveReduction_iff_reduction_c₆` — additive reduction ⟺ `Δ̃ = 0 ∧ c̃₆ = 0` (cusp).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **Among bad reduction, `c̃₄` and `c̃₆` vanish together.** If the reduced curve is singular
(`Δ̃ = 0`) then the invariant relation `1728 · Δ̃ = c̃₄³ − c̃₆²` collapses to `c̃₄³ = c̃₆²`, so over
the field `ResidueField R` the two invariants `c̃₄` and `c̃₆` are simultaneously zero. -/
theorem reduction_c₄_eq_zero_iff_c₆_eq_zero (W : WeierstrassCurve K) [IsMinimal R W]
    (hΔ : (W.reduction R).Δ = 0) :
    (W.reduction R).c₄ = 0 ↔ (W.reduction R).c₆ = 0 := by
  have hrel := (W.reduction R).c_relation
  rw [hΔ] at hrel
  have h : (W.reduction R).c₄ ^ 3 = (W.reduction R).c₆ ^ 2 := by linear_combination -hrel
  constructor
  · intro hc₄
    have hsq : (W.reduction R).c₆ ^ 2 = 0 := by rw [hc₄] at h; linear_combination -h
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq
  · intro hc₆
    have hcb : (W.reduction R).c₄ ^ 3 = 0 := by rw [hc₆] at h; linear_combination h
    exact pow_eq_zero_iff (by norm_num) |>.mp hcb

variable (R) in
/-- **Multiplicative reduction is a node, read off `c₆`.** For a minimal model, `W` has
multiplicative reduction iff the reduced curve is singular (`Δ̃ = 0`) with a nonvanishing
`c₆`-invariant (`c̃₆ ≠ 0`) — the `c₆` mirror of `hasMultiplicativeReduction_iff_reduction`. -/
theorem hasMultiplicativeReduction_iff_reduction_c₆ (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasMultiplicativeReduction R ↔ (W.reduction R).Δ = 0 ∧ (W.reduction R).c₆ ≠ 0 := by
  constructor
  · intro h
    exact ⟨((hasMultiplicativeReduction_iff_reduction R W).mp h).1, h.reduction_c₆_ne_zero⟩
  · rintro ⟨hΔ, hc₆⟩
    exact (hasMultiplicativeReduction_iff_reduction R W).mpr
      ⟨hΔ, mt (reduction_c₄_eq_zero_iff_c₆_eq_zero R W hΔ).mp hc₆⟩

variable (R) in
/-- **Additive reduction is a cusp, read off `c₆`.** For a minimal model, `W` has additive reduction
iff the reduced curve is singular (`Δ̃ = 0`) with a vanishing `c₆`-invariant (`c̃₆ = 0`) — the `c₆`
mirror of `hasAdditiveReduction_iff_reduction`. -/
theorem hasAdditiveReduction_iff_reduction_c₆ (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasAdditiveReduction R ↔ (W.reduction R).Δ = 0 ∧ (W.reduction R).c₆ = 0 := by
  constructor
  · intro h
    exact ⟨((hasAdditiveReduction_iff_reduction R W).mp h).1, h.reduction_c₆_eq_zero⟩
  · rintro ⟨hΔ, hc₆⟩
    exact (hasAdditiveReduction_iff_reduction R W).mpr
      ⟨hΔ, (reduction_c₄_eq_zero_iff_c₆_eq_zero R W hΔ).mpr hc₆⟩

end WeierstrassCurve
