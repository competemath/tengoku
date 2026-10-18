/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionNodeCusp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `c₆`-signature of node vs cusp (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  The
node/cusp classification of `ReductionNodeCusp.lean` (#490/#491) reads the bad-reduction type
off the reduced curve's discriminant `Δ̃` and `c₄`-invariant `c̃₄`:

* **multiplicative** (a **node**) ⟺ `Δ̃ = 0 ∧ c̃₄ ≠ 0`;
* **additive** (a **cusp**) ⟺ `Δ̃ = 0 ∧ c̃₄ = 0`.

It says nothing about the third invariant `c̃₆`.  This file supplies the missing `c₆` half using
Mathlib's invariant relation `c_relation : 1728 · Δ = c₄³ − c₆²`, valid over any `CommRing` and
hence over the residue field `ResidueField R`.  Applied to the reduced curve `W.reduction R` —
where in both bad cases `Δ̃ = 0` — it forces `c̃₆² = c̃₄³`, which pins down `c̃₆`:

* at a **cusp** (`c̃₄ = 0`, `Δ̃ = 0`) it gives `c̃₆² = 0`, hence `c̃₆ = 0`: **all** the reduced
  invariants `c̃₄, c̃₆, Δ̃` vanish;
* at a **node** (`c̃₄ ≠ 0`, `Δ̃ = 0`) it gives `c̃₆² = c̃₄³ ≠ 0`, hence `c̃₆ ≠ 0`.

This is the reduced-curve `c₆`-invariant face of the node/cusp dictionary, the natural sibling of
the `c₄`-only classification.  Everything is pure algebra over the residue field: it uses only
`1728 · 0 = 0` and never `1728 ≠ 0`, so it holds in **every** characteristic, and it is fully
unconditional (only `IsMinimal R W`) — no Tate-curve, valuation-extension, or Néron-model theory.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]`, in `namespace WeierstrassCurve`:

* `reduction_c₆_eq_zero_iff` — `(W.reduction R).c₆ = 0 ↔ v(c₆) < 1` (the `c₆` sibling of
  `reduction_c₄_eq_zero_iff`);
* `HasAdditiveReduction.reduction_c₆_eq_zero` — a cusp has `c̃₆ = 0`;
* `hasAdditiveReduction_iff_reduction_invariants_eq_zero` — additive reduction ⟺ all three reduced
  invariants `c̃₄, c̃₆, Δ̃` vanish;
* `HasMultiplicativeReduction.reduction_c₆_sq_eq` — a node satisfies `c̃₆² = c̃₄³`;
* `HasMultiplicativeReduction.reduction_c₆_ne_zero` — a node has `c̃₆ ≠ 0`;
* `HasMultiplicativeReduction.reduction_c₄_isSquare` — at a node `c̃₄` is a square.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **The `c₆`-invariant of the reduced curve vanishes iff `c₆` has positive valuation.**
`(W.reduction R).c₆ = 0` exactly when `v(c₆) < 1`.
The `c₆` sibling of `reduction_c₄_eq_zero_iff`. -/
theorem reduction_c₆_eq_zero_iff (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).c₆ = 0 ↔ valuation K (maximalIdeal R) W.c₆ < 1 := by
  rw [reduction_c₆_eq R W, residue_eq_zero_iff, ← integralModel_c₆_eq R W]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (integralModel R W).c₆).symm

/-- **A cusp has vanishing `c₆`.** For a minimal model with additive (cusp) reduction, the reduced
curve's `c₆`-invariant vanishes: from `Δ̃ = 0` and `c̃₄ = 0`, the invariant relation
`1728 · Δ̃ = c̃₄³ − c̃₆²` collapses to `c̃₆² = 0`. -/
theorem HasAdditiveReduction.reduction_c₆_eq_zero (W : WeierstrassCurve K) [IsMinimal R W]
    (h : W.HasAdditiveReduction R) : (W.reduction R).c₆ = 0 := by
  obtain ⟨hΔ, hc₄⟩ := (hasAdditiveReduction_iff_reduction R W).mp h
  have hrel := (W.reduction R).c_relation
  rw [hΔ, hc₄] at hrel
  have hsq : (W.reduction R).c₆ ^ 2 = 0 := by linear_combination hrel
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

variable (R) in
/-- **A cusp is exactly the total collapse of the reduced invariants.** For a minimal model,
additive (cusp) reduction holds iff all three invariants `c̃₄, c̃₆, Δ̃` of the reduced curve
vanish. -/
theorem hasAdditiveReduction_iff_reduction_invariants_eq_zero (W : WeierstrassCurve K)
    [IsMinimal R W] :
    W.HasAdditiveReduction R ↔
      (W.reduction R).c₄ = 0 ∧ (W.reduction R).c₆ = 0 ∧ (W.reduction R).Δ = 0 := by
  constructor
  · intro h
    obtain ⟨hΔ, hc₄⟩ := (hasAdditiveReduction_iff_reduction R W).mp h
    exact ⟨hc₄, h.reduction_c₆_eq_zero, hΔ⟩
  · rintro ⟨hc₄, _, hΔ⟩
    exact (hasAdditiveReduction_iff_reduction R W).mpr ⟨hΔ, hc₄⟩

/-- **At a node `c̃₆² = c̃₄³`.** For a minimal model with multiplicative (node) reduction, `Δ̃ = 0`
turns the invariant relation `1728 · Δ̃ = c̃₄³ − c̃₆²` into `c̃₆² = c̃₄³`. -/
theorem HasMultiplicativeReduction.reduction_c₆_sq_eq (W : WeierstrassCurve K) [IsMinimal R W]
    (h : W.HasMultiplicativeReduction R) :
    (W.reduction R).c₆ ^ 2 = (W.reduction R).c₄ ^ 3 := by
  obtain ⟨hΔ, _⟩ := (hasMultiplicativeReduction_iff_reduction R W).mp h
  have hrel := (W.reduction R).c_relation
  rw [hΔ] at hrel
  linear_combination hrel

/-- **A node has non-vanishing `c₆`.** For a minimal model with multiplicative (node) reduction,
`c̃₆ ≠ 0`: were `c̃₆ = 0` then `c̃₄³ = c̃₆² = 0` would force `c̃₄ = 0`, contradicting the node. -/
theorem HasMultiplicativeReduction.reduction_c₆_ne_zero (W : WeierstrassCurve K) [IsMinimal R W]
    (h : W.HasMultiplicativeReduction R) : (W.reduction R).c₆ ≠ 0 := by
  obtain ⟨_, hc₄⟩ := (hasMultiplicativeReduction_iff_reduction R W).mp h
  intro hc₆
  refine hc₄ (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ?_)
  have hsq := h.reduction_c₆_sq_eq
  rw [hc₆] at hsq
  simpa using hsq.symm

/-- **At a node `c̃₄` is a square.** For a minimal model with multiplicative (node) reduction, the
reduced `c̃₄` is a square in the residue field, in every characteristic: `c̃₄ ≠ 0` together with
`c̃₆² = c̃₄³` exhibits `c̃₄ = (c̃₆ · c̃₄⁻¹)²`. This is the positive sibling of
`reduction_c₆_ne_zero`. -/
theorem HasMultiplicativeReduction.reduction_c₄_isSquare (W : WeierstrassCurve K) [IsMinimal R W]
    (h : W.HasMultiplicativeReduction R) : IsSquare (W.reduction R).c₄ := by
  have hc₄ : (W.reduction R).c₄ ≠ 0 := ((hasMultiplicativeReduction_iff_reduction R W).mp h).2
  refine ⟨(W.reduction R).c₆ * (W.reduction R).c₄⁻¹, ?_⟩
  have h6 := h.reduction_c₆_sq_eq
  field_simp
  linear_combination -h6

end WeierstrassCurve
