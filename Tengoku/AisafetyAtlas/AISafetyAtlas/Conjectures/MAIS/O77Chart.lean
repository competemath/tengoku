module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O77Proof
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.HadamardCongruence
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.LossDerivative
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ParamSplit
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.QuadraticSplit
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.SylvesterPair
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.IndefiniteBlockPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The O77 chart, and the three inputs a splitting step consumes

MAIS-O77(b) reaches a point where the loss has to be read in coordinates adapted
to print's `2H`-dimensional variation block: the block first, a complement
after, the rung point at the origin.  `O77Proof.lean` supplies the block as a
subspace and the Hessian on it as a matrix; `ParamSplit.lean` supplies the
coordinate change along an arbitrary subspace; `LossDerivative.lean` supplies
the loss as a `C^∞` function with both derivatives computed.  This module is the
join, and it produces exactly three things.

## Primary surface

| Declaration | Content |
|---|---|
| `exists_o77_chart` | the parameter space split with the block first, and the two clauses saying the first factor is that block |
| `fderiv_o77LossCoords_eq_zero` | a saddle rung point is a critical point of the loss in coordinates |
| `fderiv_o77_chart_eq_zero` | the same, centred in the chart |
| `exists_o77_block_matrix` | the Hessian on the chart's first block as a symmetric nonsingular matrix taking both signs |
| `fderiv_fderiv_o77_chart_apply` | the chart Hessian, as the polar form of `o77HessianPolar` |
| `exists_o77_block_coords` | the linear isomorphism between the chart's first block and print's parametrisation |

## The factor the loss carries, and where it goes

Print's loss is `(1/2)‖BA − Φ‖²_F` and `AISafetyAtlas.SingularLearning.pairLoss`
is `‖BA − Φ‖²_F`, so the two differ by a factor of two; the bridge is
`rrrLoss_eq_frobeniusSq`, recorded here as `o77LossCoords_eq_pairLoss`.  The
factor is not cosmetic.  The second derivative of a Frobenius square carries a
factor of two of its own, and the two cancel: the chart Hessian is exactly the
polar form `o77HessianPolar`, and the matrix it produces is congruent to print's
own block matrix, not to twice it.  Dropping the half would have produced a
theorem about a different matrix that is symmetric, nonsingular and indefinite
all the same — a defect no build error would report.

## Congruent, not equal

The chart is built from an orthonormal basis of the block subspace, and print
parametrises the same subspace by a pair of vectors.  The two parametrisations
are injective linear maps with the same range, so they differ by a linear
isomorphism (`exists_o77_block_coords`), and the matrix delivered here is
congruent to print's rather than equal to it.  Congruence carries everything a
diagonalisation consumes: symmetry, nonsingularity, and the set of values of the
quadratic form, hence both signs.

## What is not here

No volume order, no splitting, no diagonalisation.  This module states the
Hessian's block in a chart and nothing about what the germ does.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open Module (finrank)

section Split

variable {n : ℕ}

end Split

section Chart

end Chart

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section AffineTransport

open scoped ContDiff

variable {W P : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

end AffineTransport

section Critical

open scoped ContDiff

end Critical

section ChartHessian

open scoped ContDiff

end ChartHessian

section PolarMatrix

open Matrix

end PolarMatrix

section BlockCoords

end BlockCoords

section BlockMatrix

open Matrix

end BlockMatrix

/-! ## Part (b), assembled

Every piece print's argument names is now in hand, so the assembly is a matter of
handing them to the abstracted statement of that argument,
`SingularLearning.hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block`.

The dimension bound is print's own line: `k < r < H` forces `2H ≥ 4`, and the
band lemma asks for `3`. The mode is print's own choice of "a discarded singular
mode `α > k`", taken here at the first one, `α = k`; nothing distinguishes it,
and `o77SaddleBlock_quadForm_indefinite` does not even need `k ≤ α`. -/

end AISafetyAtlas.Conjectures.MAIS
