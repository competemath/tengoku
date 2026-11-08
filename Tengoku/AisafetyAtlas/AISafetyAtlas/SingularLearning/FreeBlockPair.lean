module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.FreeBlockBand
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.PairTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The free block, read as a local pair

`FreeBlockBand.lean` proves the two-sided `Θ(ε)` band estimate for
`Q(ξ) + g(ζ)`, but on the **product** space `EuclideanSpace ℝ (Fin (p+q)) ×
EuclideanSpace ℝ (Fin s)` and inside a **product box** `‖ξ‖ ≤ δ ∧ ‖ζ‖ ≤ δ`.
`HasLocalVolumeOrder` of `LocalPair.lean` lives on a single
`EuclideanSpace ℝ (Fin n)` and measures Euclidean balls.  This module is exactly
that transfer.

## The sandwich

`euclideanProdEquiv (p+q) s` is a coordinate reindexing, so it carries Lebesgue
measure to Lebesgue measure.  Pulled back through it, the Euclidean ball of
radius `δ` about the origin is `{(ξ,ζ) | ‖ξ‖² + ‖ζ‖² < δ²}`, and that set is
squeezed between two product boxes:

* `box (δ/2) ⊆ ball δ`, because `2·(δ/2)² = δ²/2 < δ²`;
* `ball δ ⊆ box δ`, because each of `‖ξ‖²`, `‖ζ‖²` is at most their sum.

So the sublevel volume of the germ inside the Euclidean ball of radius `δ` is
bounded below by the band volume in the box of radius `δ/2` and above by the band
volume in the box of radius `δ`.  `exists_freeBlockBand_bounds` supplies a
`Θ(ε)` estimate at each of the two radii, and the two estimates close the
sandwich.

## What the constants are, and the one cosmetic adjustment

The lower constant comes from the band estimate at radius `δ/2` and the upper one
from the band estimate at radius `δ`.  These are produced by two independent
invocations of `exists_freeBlockBand_bounds`, so nothing forces `cLower ≤ cUpper`
on the nose.  `HasLocalVolumeOrder` demands that ordering, so the upper constant
is taken to be `max cLower cUpper`, which still upper-bounds the sublevel volume
and is trivially at least the lower one.  This weakens no estimate: it only
enlarges a constant that the definition already quantifies existentially.

## The radius quantifier

`HasLocalVolumeOrder` quantifies `δ` over `Ioo 0 δ₀` for a `δ₀` the witness
chooses.  No upper restriction on `δ` is needed here — the sandwich and both band
estimates hold at every positive radius — so `δ₀ = 1` is taken, and the statement
would be equally true with any positive `δ₀`.

## The pair

The pair is `(λ, m) = (1, 1)`: the band `|Q(ξ) + g(ζ)| ≤ ε` has volume linear in
`ε` with no logarithmic factor, and `volumeScale 1 1 ε = ε`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

/-! ## The scale at the pair `(1, 1)` -/

/-! ## The germ on a single Euclidean space -/

/-- The band germ of `Q(ξ) + g(ζ)` read on a single Euclidean space.

The split coordinates are recovered by `euclideanProdEquiv (p+q) s`, which is a
permutation of coordinates and nothing more, so this is the same function as the
one `FreeBlockBand.lean` studies on the product — only its domain is written as
`EuclideanSpace ℝ (Fin (p + q + s))`.-/
@[expose] public noncomputable def freeBlockGerm (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (w : EuclideanSpace ℝ (Fin (p + q + s))) : ℝ :=
  |modelBandForm p q ((euclideanProdEquiv (p + q) s).symm w).1
    + g (((euclideanProdEquiv (p + q) s).symm w).2)|

/-! ## The geometric sandwich: box `δ/2` ⊆ ball `δ` ⊆ box `δ` -/

/-! ## The sandwich in `sublevelVolume` form -/

/-! ## The local pair -/

end AISafetyAtlas.SingularLearning
