/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionSplitMultiplicativeC6

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The non-split multiplicative criterion (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  The split
multiplicative criteria `hasSplitMultiplicativeReduction_iff_isSquare` (#494) and
`hasSplitMultiplicativeReduction_iff_isSquare_neg_c₆` (#497, in `ReductionSplitMultiplicative.lean`
and `ReductionSplitMultiplicativeC6.lean`) detect **split** multiplicative reduction, for residue
characteristic `≠ 2`, by asking that `−c̃₄·c̃₆` (resp. `−c̃₆`) be a square in the residue field.
Silverman AEC VII.5.1 states both faces of the refinement; this file supplies the **non-split**
companion.

Mathlib defines split multiplicative reduction (`HasSplitMultiplicativeReduction`) but has **no**
`HasNonsplitMultiplicativeReduction` predicate, so *non-split multiplicative reduction* is spelled
`W.HasMultiplicativeReduction R ∧ ¬ W.HasSplitMultiplicativeReduction R`.  Negating the two split
criteria (both faces of one equivalence, coupled by the residue-field identity
`IsSquare (−c̃₄·c̃₆) ↔ IsSquare (−c̃₆)` proved inside #497) gives, for residue characteristic `≠ 2`:

* **non-split multiplicative** ⟺ `W` has multiplicative reduction and `¬ IsSquare (−c̃₆)`
  (equivalently `¬ IsSquare (−c̃₄·c̃₆)`).

Since a curve with multiplicative reduction is split or non-split according as `−c̃₆` is or is not a
square, this also packages the exclusive **split-or-non-split dichotomy**.

Like its split parents, this is fully unconditional apart from the residue-characteristic
hypothesis; no Tate-curve / valuation-extension / base-change theory.  (The residue characteristic
`2` case is the Artin–Schreier split criterion, Mathlib's remaining open `TODO`, and is out of
scope.)

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]` and `[NeZero (2 : ResidueField R)]`, in
`namespace WeierstrassCurve`:

* `hasMultiplicativeReduction_and_not_split_iff_not_isSquare_neg_c₆` — `W` has non-split
  multiplicative reduction iff it has multiplicative reduction and `−c̃₆` is **not** a square;
* `hasMultiplicativeReduction_and_not_split_iff_not_isSquare` — the `−c̃₄·c̃₆` form;
* `HasMultiplicativeReduction.hasSplitMultiplicativeReduction_or_not` — the exhaustive
  split-or-non-split dichotomy for multiplicative reduction.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1.
-/

open IsLocalRing

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- **Non-split multiplicative reduction is detected by `c₆` alone (residue char ≠ 2).**  When the
residue field has characteristic `≠ 2`, `W` has non-split multiplicative reduction — i.e.
multiplicative but not split — iff it has multiplicative reduction and `−c̃₆` is **not** a square in
the residue field.  This is the non-split companion of
`hasSplitMultiplicativeReduction_iff_isSquare_neg_c₆` (#497), Silverman AEC VII.5.1. -/
theorem hasMultiplicativeReduction_and_not_split_iff_not_isSquare_neg_c₆
    [NeZero (2 : ResidueField R)] (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.HasMultiplicativeReduction R ∧ ¬ W.HasSplitMultiplicativeReduction R) ↔
      W.HasMultiplicativeReduction R ∧ ¬ IsSquare (-(W.reduction R).c₆) := by
  refine and_congr_right fun hmult => ?_
  rw [hasSplitMultiplicativeReduction_iff_isSquare_neg_c₆ R W, not_and]
  exact ⟨fun h => h hmult, fun h _ => h⟩

variable (R) in
/-- **Non-split multiplicative reduction via the discriminant `−c̃₄·c̃₆` (residue char ≠ 2).**  The
`−c̃₄·c̃₆` form of `hasMultiplicativeReduction_and_not_split_iff_not_isSquare_neg_c₆`: the non-split
companion of `hasSplitMultiplicativeReduction_iff_isSquare` (#494). -/
theorem hasMultiplicativeReduction_and_not_split_iff_not_isSquare
    [NeZero (2 : ResidueField R)] (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.HasMultiplicativeReduction R ∧ ¬ W.HasSplitMultiplicativeReduction R) ↔
      W.HasMultiplicativeReduction R ∧ ¬ IsSquare (-(W.reduction R).c₄ * (W.reduction R).c₆) := by
  refine and_congr_right fun hmult => ?_
  rw [hasSplitMultiplicativeReduction_iff_isSquare R W, not_and]
  exact ⟨fun h => h hmult, fun h _ => h⟩

/-- **The split-or-non-split dichotomy for multiplicative reduction.**  A curve with multiplicative
reduction has either split multiplicative reduction or non-split multiplicative reduction
(`mult ∧ ¬split`) — the two cases are exhaustive, and being contradictory they are exclusive.  In
residue characteristic `≠ 2` which case holds is governed by whether `−c̃₆` is a square, via
`hasMultiplicativeReduction_and_not_split_iff_not_isSquare_neg_c₆`.

⚠️ **This statement used to carry `[IsMinimal R W]` and it was dead** — the instance occurred in
neither the remainder of the type nor the proof term, measured on the elaborated environment at
`2e44940` (`#1272`).  The dichotomy is `rcases em _`, i.e. excluded middle on
`HasSplitMultiplicativeReduction`, and neither predicate takes minimality as an instance argument.
⚠️ The two `iff` results above it **do** use `[IsMinimal R W]`; this is the one that does not, and
the asymmetry is the point rather than an oversight. -/
theorem HasMultiplicativeReduction.hasSplitMultiplicativeReduction_or_not
    {W : WeierstrassCurve K} (hmult : W.HasMultiplicativeReduction R) :
    W.HasSplitMultiplicativeReduction R ∨
      (W.HasMultiplicativeReduction R ∧ ¬ W.HasSplitMultiplicativeReduction R) := by
  rcases em (W.HasSplitMultiplicativeReduction R) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hmult, h⟩

end WeierstrassCurve
