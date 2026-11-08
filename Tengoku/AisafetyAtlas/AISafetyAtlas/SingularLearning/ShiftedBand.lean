module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.IndefiniteBand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Level-uniform bands of an indefinite quadratic form

`IndefiniteBand.lean` computes the local volume order of `|Q|` at the origin,
where `Q = ‖u‖² - ‖v‖²` is the nondegenerate indefinite model form of signature
`(p, q)`.  Every estimate there is about the band around level **zero**, because
that is the only band `HasLocalVolumeOrder` sees: a sublevel set of a
nonnegative germ is a band around zero by construction.

This module proves the **level-uniform** statement: the band `|Q(w) - c| ≤ ε`
inside the ball of radius `δ`, for an *arbitrary* level `c`, has volume at most
`shiftedBandConst p q δ * ε` — one constant serving every level at once.  That
is strictly more than the level-zero estimate gives, and it is not obtainable
from it by translation, because translating the level does not translate the
window.

## Why the argument is different from the level-zero one

The level-zero proof goes through a Gaussian-Laplace transform, which needs the
germ's degree-two homogeneity (`modelBandGerm_smul`).  A band around a nonzero
level is not homogeneous, so that route is unavailable and the estimate has to
be done directly on the set.

The direct argument, in the first block:

* fix `v`; the slice is `{u : ‖u‖² ∈ [c + ‖v‖² - ε, c + ‖v‖² + ε]}`, a spherical
  shell of radii `ρ₋ ≤ ρ₊` clipped to the window (`measureReal_sliceBand_le`);
* the clipped radii satisfy `ρ₊² - ρ₋² ≤ 2ε` and `ρ₊ ≤ δ` whatever the level is,
  which is where the uniformity in `c` comes from;
* `pow_sub_pow_le_mul_sq_sub_sq` turns that into
  `ρ₊^p - ρ₋^p ≤ p · δ^(p-2) · (ρ₊² - ρ₋²)`, so the shell volume is `≲ ε`;
* Fubini over the second block (`measure_bandWindow_le`) multiplies by the
  volume of the `q`-window.

The hypothesis `2 ≤ p` enters exactly once, in the exponent `δ^(p-2)`, and it is
the same place the level-zero proof needs it.  As there, `p = 1` is handled by
the block swap (`shiftedBandVolume_le_of_three_le`), which reuses
`euclideanSwap` rather than redoing the estimate: the *signed* form changes sign
under the swap, and `|(-x) - (-c)| = |x - c|`.

## What the lower bound can and cannot say

`shiftedBandVolume_ge` is the matching lower bound, and it is necessarily
conditional on the level: at a level the form does not attain inside the ball
the band is empty and no positive lower bound exists.  The condition taken here
is `|c| ≤ δ²/32` together with `ε ≤ δ²/4`, which leaves room for a whole annulus
`δ/4 ≤ ‖v‖ ≤ δ/2` of the second block, each of whose slices sweeps a shell of
the first.  `exists_shiftedBand_bounds` packages the two sides with a single
ordered pair of constants.

**This module states nothing about `HasLocalVolumeOrder`.**  A level-uniform
band estimate is a different object from a local pair, and identifying the two
would be a claim this file does not prove.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-! ## Shell volumes in one block -/

/-! ## The shifted band -/

/-- The nondegenerate indefinite form `‖u‖² - ‖v‖²` of signature `(p, q)`, read
on the ambient space through the coordinate split.  `modelBandGerm` is its
absolute value; this module needs the signed form, because a band around a
nonzero level is not a sublevel set of the germ.-/
@[expose] public noncomputable def modelBandForm (p q : ℕ)
    (w : EuclideanSpace ℝ (Fin (p + q))) : ℝ :=
  ‖((splitLE p q).symm w).1‖ ^ 2 - ‖((splitLE p q).symm w).2‖ ^ 2

/-- **The band of half-width `ε` around the level `c`**, inside the closed ball
of radius `δ` about the origin.-/
@[expose] public noncomputable def shiftedBandSet (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin (p + q))) :=
  {w | ‖w‖ ≤ δ ∧ |modelBandForm p q w - c| ≤ ε}

/-- The band read in split coordinates and enlarged from the Euclidean ball to
the product window `‖u‖ ≤ δ`, `‖v‖ ≤ δ`.  The enlargement costs a constant and
buys a set Fubini can slice.-/
@[expose] public noncomputable def bandWindow (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  {z | ‖z.1‖ ≤ δ ∧ ‖z.2‖ ≤ δ ∧ |‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 - c| ≤ ε}

/-- The level-uniform upper constant of signature `(p, q)` at radius `δ`.  It
depends on the radius and on the two block dimensions, and on nothing else — in
particular not on the level `c`, which is the whole point.-/
@[expose] public noncomputable def shiftedBandConst (p q : ℕ) (δ : ℝ) : ℝ :=
  2 * (p : ℝ) * δ ^ (p - 2) * δ ^ q *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal

/-- The real-valued volume of the band of half-width `ε` around the level `c`,
inside the closed ball of radius `δ` about the origin.-/
@[expose] public noncomputable def shiftedBandVolume (p q : ℕ) (c δ ε : ℝ) : ℝ :=
  (volume (shiftedBandSet p q c δ ε)).toReal

/-! ## The block swap, and the `p = 1` case -/

/-! ## The matching lower bound

The upper bound is the half the level-uniformity is about, and it holds for
every level.  A lower bound cannot: at a level the form does not attain inside
the ball the band is empty.  The statement below therefore restricts the level
to `|c| ≤ δ²/32`, which is enough room to place a whole annulus of the second
block inside the window, and asks `ε ≤ δ²/4` so that the shell it sweeps in the
first block still fits.
-/

/-- The subset of the band that the lower bound sweeps: the second block runs
over the annulus `δ/4 ≤ ‖v‖ ≤ δ/2`, and for each such `v` the first block runs
over the shell `‖u‖² ∈ [c + ‖v‖², c + ‖v‖² + ε]`.-/
@[expose] public noncomputable def bandCore (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  {z | δ / 4 ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ δ / 2 ∧
    c + ‖z.2‖ ^ 2 ≤ ‖z.1‖ ^ 2 ∧ ‖z.1‖ ^ 2 ≤ c + ‖z.2‖ ^ 2 + ε}

/-- The level-uniform lower constant: the annulus in the second block times the
shell in the first.-/
@[expose] public noncomputable def shiftedBandLowerConst (p q : ℕ) (δ : ℝ) : ℝ :=
  (δ / 6) ^ (p - 1) / (2 * δ) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal *
    (((δ / 2) ^ q - (δ / 4) ^ q) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal)

end AISafetyAtlas.SingularLearning
