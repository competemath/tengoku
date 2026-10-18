/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ReductionNodeCusp
import Tengoku.Seed.Algebra.QuadraticDiscriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Split multiplicative reduction via the discriminant (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`).  Mathlib
defines split multiplicative reduction (`HasSplitMultiplicativeReduction`,
`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`) by asking that the quadratic
`c₄ T² + a₁ c₄ T − (54 b₆ − 3 b₂ b₄ + a₂ c₄)` of the integral minimal model **splits** in the
residue field — the two tangent directions at the node are rational over the residue field.

Mathlib leaves a standing `TODO` there: *"add characterization in terms of the discriminant when
the characteristic is not 2"*.  This file closes it.  For a quadratic over a field of residue
characteristic `≠ 2`, splitting is equivalent to its discriminant being a square, and here the
discriminant has the clean closed form

```
b² − 4ac = −(W.reduction R).c₄ · (W.reduction R).c₆
```

(a pure `ring` identity in the coefficients `aᵢ`, using `b₂ = a₁²+4a₂`, `c₄ = b₂²−24b₄`,
`c₆ = −b₂³+36b₂b₄−216b₆`).  So, for a curve with multiplicative reduction and residue
characteristic `≠ 2`,

* **split multiplicative** ⟺ `IsSquare (−c̃₄ · c̃₆)`  in the residue field.

This is the reduced-curve-invariant face of the split/non-split refinement, the natural companion
of the node/cusp trichotomy (`ReductionNodeCusp.lean`, #491).  It is fully unconditional apart from
the residue-characteristic hypothesis; no Tate-curve / valuation-extension / base-change theory.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]` and `[NeZero (2 : ResidueField R)]`, in
`namespace WeierstrassCurve`:

* `discrim_splitMultiplicative_eq` — the discriminant of the split-multiplicative quadratic (over
  the residue field) equals `−(W.reduction R).c₄ * (W.reduction R).c₆`;
* `hasSplitMultiplicativeReduction_iff_isSquare` — `W` has split multiplicative reduction iff `W`
  has multiplicative reduction and `−c̃₄ · c̃₆` is a square in the residue field.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1.
-/

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- The split-multiplicative quadratic of the integral minimal model, mapped to the residue field,
written in the canonical form `C a * X ^ 2 + C b * X + C c`, with coefficients read off the reduced
curve's invariants. -/
theorem splitMultiplicative_poly_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (Polynomial.map (algebraMap R (ResidueField R))
        (C (integralModel R W).c₄ * X ^ 2 + C ((integralModel R W).a₁ * (integralModel R W).c₄) * X
          - C (54 * (integralModel R W).b₆ - 3 * (integralModel R W).b₂ * (integralModel R W).b₄
              + (integralModel R W).a₂ * (integralModel R W).c₄))) =
      C (W.reduction R).c₄ * X ^ 2 + C ((W.reduction R).a₁ * (W.reduction R).c₄) * X
        + C (-(54 * (W.reduction R).b₆ - 3 * (W.reduction R).b₂ * (W.reduction R).b₄
            + (W.reduction R).a₂ * (W.reduction R).c₄)) := by
  -- identify each mapped coefficient with the reduced curve's invariant
  have e1 : algebraMap R (ResidueField R) (integralModel R W).c₄ = (W.reduction R).c₄ := by
    rw [ResidueField.algebraMap_eq, ← reduction_c₄_eq R W]
  have e2 : algebraMap R (ResidueField R) ((integralModel R W).a₁ * (integralModel R W).c₄)
      = (W.reduction R).a₁ * (W.reduction R).c₄ := by
    rw [map_mul, ResidueField.algebraMap_eq, ← reduction_a₁_eq R W, ← reduction_c₄_eq R W]
  have e3 : algebraMap R (ResidueField R) (54 * (integralModel R W).b₆
        - 3 * (integralModel R W).b₂ * (integralModel R W).b₄
        + (integralModel R W).a₂ * (integralModel R W).c₄)
      = 54 * (W.reduction R).b₆ - 3 * (W.reduction R).b₂ * (W.reduction R).b₄
        + (W.reduction R).a₂ * (W.reduction R).c₄ := by
    simp only [map_add, map_sub, map_mul, map_ofNat, ResidueField.algebraMap_eq,
      ← reduction_a₂_eq R W, ← reduction_b₂_eq R W, ← reduction_b₄_eq R W, ← reduction_b₆_eq R W,
      ← reduction_c₄_eq R W]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, e1, e2, e3]
  rw [sub_eq_add_neg, ← C_neg]

variable (R) in
/-- **The discriminant of the split-multiplicative quadratic.** Over the residue field it equals
`−(W.reduction R).c₄ · (W.reduction R).c₆`.  This is a universal `ring` identity in the coefficients
`aᵢ` of the reduced curve, and is the clean invariant form the `char ≠ 2` splitting criterion is
stated against. -/
theorem discrim_splitMultiplicative_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    discrim (W.reduction R).c₄ ((W.reduction R).a₁ * (W.reduction R).c₄)
        (-(54 * (W.reduction R).b₆ - 3 * (W.reduction R).b₂ * (W.reduction R).b₄
            + (W.reduction R).a₂ * (W.reduction R).c₄)) =
      -(W.reduction R).c₄ * (W.reduction R).c₆ := by
  simp only [discrim, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

variable (R) in
/-- **Split multiplicative reduction is detected by a discriminant square (residue char ≠ 2).**
When the residue field has characteristic `≠ 2`, `W` has split multiplicative reduction iff it has
multiplicative reduction and `−c̃₄ · c̃₆` is a square in the residue field.  This closes the
`TODO` in `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` asking for the discriminant
characterization. -/
theorem hasSplitMultiplicativeReduction_iff_isSquare [NeZero (2 : ResidueField R)]
    (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasSplitMultiplicativeReduction R ↔
      W.HasMultiplicativeReduction R ∧
        IsSquare (-(W.reduction R).c₄ * (W.reduction R).c₆) := by
  rw [hasSplitMultiplicativeReduction_iff]
  constructor
  · -- split ⇒ multiplicative reduction together with the discriminant being a square
    rintro ⟨hmult, hsplit⟩
    refine ⟨hmult, ?_⟩
    have ha : (W.reduction R).c₄ ≠ 0 := by
      rw [Ne, reduction_c₄_eq_zero_iff R W, hmult.multiplicativeReduction]
      exact lt_irrefl 1
    rw [splitMultiplicative_poly_eq R W] at hsplit
    rw [← discrim_splitMultiplicative_eq R W]
    have hdeg : (C (W.reduction R).c₄ * X ^ 2 + C ((W.reduction R).a₁ * (W.reduction R).c₄) * X
        + C (-(54 * (W.reduction R).b₆ - 3 * (W.reduction R).b₂ * (W.reduction R).b₄
            + (W.reduction R).a₂ * (W.reduction R).c₄)) : (ResidueField R)[X]).degree ≠ 0 := by
      rw [degree_quadratic ha]; decide
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero hdeg
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
    refine ⟨2 * (W.reduction R).c₄ * x + (W.reduction R).a₁ * (W.reduction R).c₄, ?_⟩
    rw [← pow_two]
    exact discrim_eq_sq_of_quadratic_eq_zero (by linear_combination hx)
  · -- multiplicative reduction and a square discriminant ⇒ the quadratic splits
    rintro ⟨hmult, hsq⟩
    refine ⟨hmult, ?_⟩
    have ha : (W.reduction R).c₄ ≠ 0 := by
      rw [Ne, reduction_c₄_eq_zero_iff R W, hmult.multiplicativeReduction]
      exact lt_irrefl 1
    rw [splitMultiplicative_poly_eq R W]
    rw [← discrim_splitMultiplicative_eq R W] at hsq
    obtain ⟨s, hs⟩ := hsq
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs, ← pow_two, sq]⟩
    refine Splits.of_natDegree_eq_two (natDegree_quadratic ha) (x := x) ?_
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination hx

end WeierstrassCurve
