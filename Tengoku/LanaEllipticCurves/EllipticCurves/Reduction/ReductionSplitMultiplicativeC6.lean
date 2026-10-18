/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionSplitMultiplicative
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionC6Signature

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `c₆`-only split multiplicative criterion (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  The
discriminant characterization `hasSplitMultiplicativeReduction_iff_isSquare`
(`ReductionSplitMultiplicative.lean`, #494) detects split multiplicative reduction, for residue
characteristic `≠ 2`, by asking that `−c̃₄ · c̃₆` be a square in the residue field.  This file
rewrites that criterion in the **single invariant `c̃₆`**, matching the `c₆`-only node/cusp iffs of
`ReductionC6Criteria.lean` (#496):

* **split multiplicative** ⟺ `W` has multiplicative reduction and `IsSquare (−c̃₆)`.

The reduction is pure residue-field algebra.  At a node (multiplicative reduction) `Δ̃ = 0` with
`c̃₄ ≠ 0`, so Mathlib's invariant relation gives `c̃₆² = c̃₄³`
(`HasMultiplicativeReduction.reduction_c₆_sq_eq`, #495).  Hence
`c̃₄ = c̃₆² / c̃₄² = (c̃₆ · c̃₄⁻¹)²` is a **nonzero square**, and since `−c̃₄ · c̃₆ = c̃₄ · (−c̃₆)`,
multiplying by the nonzero square `c̃₄` preserves squareness:
`IsSquare (−c̃₄ · c̃₆) ↔ IsSquare (−c̃₆)`.

Like its `c₄ · c₆` parent this is fully unconditional apart from the residue-characteristic
hypothesis; no Tate-curve / valuation-extension / base-change theory.  (The residue characteristic
`2` case is the Artin–Schreier split criterion, Mathlib's remaining open `TODO`, and is out of
scope.)

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]` and `[NeZero (2 : ResidueField R)]`, in
`namespace WeierstrassCurve`:

* `hasSplitMultiplicativeReduction_iff_isSquare_neg_c₆` — `W` has split multiplicative reduction iff
  `W` has multiplicative reduction and `−c̃₆` is a square in the residue field.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsLocalRing

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- Multiplying by a nonzero square preserves squareness in a field: if `a ≠ 0` is a square then
`a * b` is a square iff `b` is. -/
private theorem isSquare_mul_left_iff_of_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0)
    (h : IsSquare a) : IsSquare (a * b) ↔ IsSquare b := by
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := left_ne_zero_of_mul ha
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t * s⁻¹, by field_simp; linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨s * t, by rw [ht]; ring⟩

variable (R) in
/-- **Split multiplicative reduction is detected by `c₆` alone (residue char ≠ 2).**  When the
residue field has characteristic `≠ 2`, `W` has split multiplicative reduction iff it has
multiplicative reduction and `−c̃₆` is a square in the residue field.  This is the `c₆`-only form
of `hasSplitMultiplicativeReduction_iff_isSquare`: at a node `c̃₄` is a nonzero square
(`c̃₄ = c̃₆²/c̃₄²` from `c̃₆² = c̃₄³`), so `IsSquare (−c̃₄·c̃₆) ↔ IsSquare (−c̃₆)`. -/
theorem hasSplitMultiplicativeReduction_iff_isSquare_neg_c₆ [NeZero (2 : ResidueField R)]
    (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasSplitMultiplicativeReduction R ↔
      W.HasMultiplicativeReduction R ∧ IsSquare (-(W.reduction R).c₆) := by
  rw [hasSplitMultiplicativeReduction_iff_isSquare R W]
  refine and_congr_right fun hmult => ?_
  -- at a node `c̃₄` is a nonzero square, and `−c̃₄·c̃₆ = c̃₄·(−c̃₆)`
  have hc₄ : (W.reduction R).c₄ ≠ 0 := ((hasMultiplicativeReduction_iff_reduction R W).mp hmult).2
  have hsq : IsSquare (W.reduction R).c₄ := hmult.reduction_c₄_isSquare
  have hrw : -(W.reduction R).c₄ * (W.reduction R).c₆
      = (W.reduction R).c₄ * (-(W.reduction R).c₆) := by ring
  rw [hrw, isSquare_mul_left_iff_of_ne_zero hc₄ hsq]

end WeierstrassCurve
