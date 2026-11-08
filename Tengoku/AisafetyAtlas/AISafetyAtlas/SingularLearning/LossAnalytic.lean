module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.Coordinates
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.Loss
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.MatrixAnalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reduced-rank loss is real-analytic

This module proves that the germ `MAIS-O70` is about — the reduced-rank
population loss, read in the Euclidean coordinates of `Coordinates.lean` — is
real-analytic at every point.

## Why the module exists

`ZetaPair.lean` records, in "Why there is no general bridge here", that the
general passage from the ball-volume local pair to the zeta/pole-order local pair
is **false**: `HasExactLocalPair` constrains only the leading behaviour of the
sublevel volume, and a logarithmic correction to it turns the pole into a branch
point. The hypothesis print carries, and the one a general form drops,
is that `K` is nonnegative and **real-analytic**.

What the atlas states instead is `O70ZetaPoleBridge`, the same passage at the O70
germs only. The reason to believe that narrow form is precisely that those germs
satisfy print's missing hypothesis. Until now that reason was prose. This module
machine-checks it: `analyticAt_rrrLoss_symm_coords` is the analyticity of
`rrrLossCoords M N H C`, and `rrrLoss_nonneg` (in `Loss.lean`) is the
nonnegativity, so the pair of hypotheses `MAIS-A6.tex` `def:local` carries is
discharged for the O70 germs.

It does not prove the bridge — resolution of singularities is not in the atlas —
and it is not evidence that the bridge's *proof* is within reach. It removes one
specific way the narrowed bridge could have been vacuous or false: a bridge
narrowed to germs that did not in fact satisfy print's hypothesis would have been
narrowed to nothing.

## The argument

`rrrLoss_eq_sum_sq` writes the loss as `½ ∑ᵢ ∑ⱼ (BA − C)ᵢⱼ²`, and each entry of
`BA − C` is `∑ₖ Bᵢₖ Aₖⱼ − Cᵢⱼ`. So the loss is a *polynomial* in the entries of
`(A, B)` — degree four, with no denominators — and analyticity is closure of
`AnalyticAt` under finite sums, products and powers. No Gaussian integral
survives into the proof: the integral is discharged once, in `Loss.lean`.

`analyticAt_rrrLoss_of_entries` is the statement in that form, over an arbitrary
real normed space of parameters, and the two concrete corollaries instantiate it:

* `analyticAt_rrrLoss_pair`, on the matrix pair itself, with the Frobenius normed
  instances `MatrixAnalytic.lean` uses (matrices carry no global normed instance
  in the pinned Mathlib, so some choice has to be made; analyticity is a property
  of the topology, and all norms on a finite-dimensional real space are
  equivalent, so nothing depends on the choice);
* `analyticAt_rrrLoss_symm_coords`, in Euclidean coordinates, which is the one the
  local-pair machinery consumes.

The coordinate form is available only because `matrixPairEquiv` is a genuine
`≃ₗ[ℝ]` and not merely a `MeasurableEquiv`: each coordinate of the parameter is
read off by `matrixPairEquiv_symm_apply` as a single entry of `A` or `B`, so an
entry of the parameter matrices is a *coordinate functional* on
`EuclideanSpace ℝ (Fin (H * N + M * H))`, hence continuous linear, hence analytic.
Had `Coordinates.lean` supplied only the measurable packaging, this step would
have no proof, and the module would stop here.

## Where the `rrrLossCoords` form lives

`rrrLossCoords` is defined in `Conjectures/MAIS/O70.lean`, which imports this
layer, so the statement literally about it cannot live here. It is definitionally
`fun x => rrrLoss C ((matrixPairEquiv M N H).symm x).1 ((matrixPairEquiv M N H).symm x).2`,
which is what `analyticAt_rrrLoss_symm_coords` is stated about, so the O70-side
corollary is that theorem applied unchanged.
-/

namespace AISafetyAtlas.SingularLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M N H : ℕ}

/-! ## The loss as a polynomial in the entries -/

/-! ## On the matrix pair

Matrices carry no global normed instance in the pinned Mathlib, so the statement
on the parameter space itself needs a choice of norm. It is the same Frobenius
pair `MatrixAnalytic.lean` installs, and nothing depends on the choice. -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

end Frobenius

/-! ## In Euclidean coordinates

The form the local-pair machinery consumes. Each coordinate of the parameter is a
single entry of `A` or of `B`, by `matrixPairEquiv_symm_apply`, so the entry maps
are the coordinate functionals of `EuclideanSpace ℝ (Fin (H * N + M * H))`. -/

end AISafetyAtlas.SingularLearning
