/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionNodeCusp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bad reduction and the exclusive reduction-type trichotomy (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  Mathlib
proves that the three reduction types are **exhaustive** — one of good / multiplicative / additive
always holds (`hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction`) — and
provides the six pairwise **mutual-exclusivity** lemmas
(`HasGoodReduction.not_hasMultiplicativeReduction`, etc.).  But it packages neither the combined
"exactly one of" statement nor a `¬ HasGoodReduction ↔ …` characterization of **bad** reduction.

This file supplies both, completing the reduction-type dictionary alongside the node/cusp
classification of `ReductionNodeCusp.lean` (#490/#491):

* **bad reduction = multiplicative or additive**
  (`not_hasGoodReduction_iff_hasMultiplicativeReduction_or_hasAdditiveReduction`);
* **bad ⟺ the reduced curve is singular** `Δ̃ = 0`
  (`not_hasGoodReduction_iff_reduction_Δ_eq_zero`), the complement of
  `hasGoodReduction_iff_reduction_Δ_ne_zero`;
* the **exclusive trichotomy** `hasGoodReduction_trichotomy` — exactly one of the three types holds;
* and the three "one type is the complement of the other two" equivalences.

Everything is pure propositional bookkeeping over the exhaustive `∨`, the six negation lemmas, and
the merged `Δ̃ ≠ 0` good-reduction criterion.  It is fully unconditional (only `IsMinimal R W`) and
needs no Tate-curve / valuation-extension / Néron-model theory.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]`, in `namespace WeierstrassCurve`:

* `not_hasGoodReduction_iff_hasMultiplicativeReduction_or_hasAdditiveReduction`;
* `not_hasGoodReduction_iff_reduction_Δ_eq_zero`;
* `hasGoodReduction_trichotomy`;
* `hasGoodReduction_iff_not_multiplicative_and_not_additive`;
* `hasMultiplicativeReduction_iff_not_good_and_not_additive`;
* `hasAdditiveReduction_iff_not_good_and_not_multiplicative`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **Bad reduction is exactly multiplicative-or-additive reduction.** For a minimal model, failing
to have good reduction is equivalent to having one of the two bad types. -/
theorem not_hasGoodReduction_iff_hasMultiplicativeReduction_or_hasAdditiveReduction
    (W : WeierstrassCurve K) [IsMinimal R W] :
    ¬ W.HasGoodReduction R ↔
      W.HasMultiplicativeReduction R ∨ W.HasAdditiveReduction R := by
  constructor
  · intro h
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
      (W := W) with hg | h'
    · exact absurd hg h
    · exact h'
  · rintro (h | h)
    · exact h.not_hasGoodReduction
    · exact h.not_hasGoodReduction

variable (R) in
/-- **Bad reduction ⟺ the reduced curve is singular.** For a minimal model, `W` fails to have good
reduction exactly when the discriminant of the reduced curve vanishes (`Δ̃ = 0`) — the complement of
`hasGoodReduction_iff_reduction_Δ_ne_zero`. -/
theorem not_hasGoodReduction_iff_reduction_Δ_eq_zero (W : WeierstrassCurve K) [IsMinimal R W] :
    ¬ W.HasGoodReduction R ↔ (W.reduction R).Δ = 0 := by
  rw [hasGoodReduction_iff_reduction_Δ_ne_zero R W, not_not]

variable (R) in
/-- **The exclusive reduction-type trichotomy.** For a minimal model, exactly one of good,
multiplicative, additive reduction holds. -/
theorem hasGoodReduction_trichotomy (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.HasGoodReduction R ∧ ¬ W.HasMultiplicativeReduction R ∧ ¬ W.HasAdditiveReduction R) ∨
      (¬ W.HasGoodReduction R ∧ W.HasMultiplicativeReduction R ∧ ¬ W.HasAdditiveReduction R) ∨
      (¬ W.HasGoodReduction R ∧ ¬ W.HasMultiplicativeReduction R ∧ W.HasAdditiveReduction R) := by
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
    (W := W) with h | h | h
  · exact Or.inl ⟨h, h.not_hasMultiplicativeReduction, h.not_hasAdditiveReduction⟩
  · exact Or.inr (Or.inl ⟨h.not_hasGoodReduction, h, h.not_hasAdditiveReduction⟩)
  · exact Or.inr (Or.inr ⟨h.not_hasGoodReduction, h.not_hasMultiplicativeReduction, h⟩)

variable (R) in
/-- **Good reduction is the complement of the two bad types.** -/
theorem hasGoodReduction_iff_not_multiplicative_and_not_additive
    (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasGoodReduction R ↔
      ¬ W.HasMultiplicativeReduction R ∧ ¬ W.HasAdditiveReduction R := by
  constructor
  · intro h
    exact ⟨h.not_hasMultiplicativeReduction, h.not_hasAdditiveReduction⟩
  · rintro ⟨hm, ha⟩
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
      (W := W) with h | h | h
    · exact h
    · exact absurd h hm
    · exact absurd h ha

variable (R) in
/-- **Multiplicative reduction is the complement of good and additive.** -/
theorem hasMultiplicativeReduction_iff_not_good_and_not_additive
    (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasMultiplicativeReduction R ↔
      ¬ W.HasGoodReduction R ∧ ¬ W.HasAdditiveReduction R := by
  constructor
  · intro h
    exact ⟨h.not_hasGoodReduction, h.not_hasAdditiveReduction⟩
  · rintro ⟨hg, ha⟩
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
      (W := W) with h | h | h
    · exact absurd h hg
    · exact h
    · exact absurd h ha

variable (R) in
/-- **Additive reduction is the complement of good and multiplicative.** -/
theorem hasAdditiveReduction_iff_not_good_and_not_multiplicative
    (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasAdditiveReduction R ↔
      ¬ W.HasGoodReduction R ∧ ¬ W.HasMultiplicativeReduction R := by
  constructor
  · intro h
    exact ⟨h.not_hasGoodReduction, h.not_hasMultiplicativeReduction⟩
  · rintro ⟨hg, hm⟩
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
      (W := W) with h | h | h
    · exact absurd h hg
    · exact absurd h hm
    · exact h

end WeierstrassCurve
