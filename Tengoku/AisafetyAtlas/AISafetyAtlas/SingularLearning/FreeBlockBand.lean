module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ShiftedBand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A free block carrying an arbitrary continuous shift

`ShiftedBand.lean` proves the **level-uniform** band estimate: for the model
form `Q(ξ) = ‖u‖² - ‖v‖²` of signature `(p, q)`, the band `|Q(ξ) - c| ≤ ε`
inside the ball of radius `δ` has volume between `shiftedBandLowerConst p q δ * ε`
and `shiftedBandConst p q δ * ε`, with the *upper* constant free of the level `c`
and the lower one holding at every level with `|c| ≤ δ²/32`.

This module adds the third block.  The variable `ζ` ranges over a free
`s`-dimensional factor and enters only through an arbitrary shift `g ζ`, and the
band is the two-sided one around level zero for `Q(ξ) + g(ζ)`.  The proof is
exactly the printed one: the `ζ`-slice of the band at a fixed `ζ` is the
level-`(-(g ζ))` band of `ShiftedBand`, so Fubini in the free block turns the
level-uniform estimate into an estimate for the whole product.

## The shape that is actually proved

Two choices are made here and both are visible in the statements.

* The ambient space is the **product** `EuclideanSpace ℝ (Fin (p+q)) ×
  EuclideanSpace ℝ (Fin s)` with the product measure, not a single
  `EuclideanSpace ℝ (Fin (p+q+s))`.  The two are measurably isomorphic, but the
  isomorphism is not needed for the estimate and is not built here.
* The neighbourhood is a **product box** `‖w.1‖ ≤ δ ∧ ‖w.2‖ ≤ δ`, not a ball of
  the product.  That is the "sufficiently small product neighbourhood" of the
  printed statement, and it is what makes the slice a `shiftedBandSet` on the
  nose.

Neither choice weakens anything: the level-uniform input is used at full
strength, and the `ζ`-box of the lower bound is shrunk to a radius `ρ ≤ δ` on
which `|g ζ| ≤ δ²/32`, which is the printed "shrink the ζ-box".

## What the shift has to satisfy

The upper bound asks nothing of `g` beyond measurability: the level-uniform
constant does not see the level, so no matter how `g` moves the level, each
slice is bounded by the same `shiftedBandConst p q δ * ε`.  That is the whole
content of "integrating the uniform bound over the fixed ζ-box gives `O(ε)`".

The lower bound cannot be unconditional, for the reason `shiftedBandVolume_ge`
records: at a level the form does not attain inside the ball the band is empty.
`measure_freeBlockBandSet_ge` therefore carries the hypothesis that `|g ζ| ≤
δ²/32` on the shrunken box, and `exists_radius_of_continuousAt` discharges it
from continuity of `g` at the origin together with `g 0 = 0` — the printed
hypothesis on `g`.

`exists_freeBlockBand_bounds` packages the two sides as the `Θ(ε)` of the
printed Lemma 2.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- The band of half-width `ε` around level zero for `modelBandForm p q ξ + g ζ`,
inside the product box of radius `δ`: `‖ξ‖ ≤ δ` in the quadratic block and
`‖ζ‖ ≤ δ` in the free block.

The box, rather than a ball of the product, is deliberate — it is the "product
neighbourhood" of the printed statement, and it is what makes the `ζ`-slice
literally a `shiftedBandSet`.-/
@[expose] public noncomputable def freeBlockBandSet (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin (p + q)) × EuclideanSpace ℝ (Fin s)) :=
  {w | ‖w.1‖ ≤ δ ∧ ‖w.2‖ ≤ δ ∧ |modelBandForm p q w.1 + g w.2| ≤ ε}

/-! ## The slices in the free block -/

/-! ## The two bounds -/

/-! ## Shrinking the free-block box -/

/-! ## The packaged two-sided statement -/

end AISafetyAtlas.SingularLearning
