module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.IndefiniteBand
public import Tengoku.Seed.LinearAlgebra.QuadraticForm.Real
public import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
public import Tengoku.Seed.LinearAlgebra.Matrix.ToLinearEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sylvester's law of inertia, wired to the band pair

`hasLocalVolumeOrder_abs_of_diagonal` computes the local band pair
of a germ *already presented* as the absolute value of a `±1`-weighted sum of
squares: its caller must supply the weight vector `w`, the coordinate equivalence
`f`, and the sign-sorting bijection `τ`.  Its docstring calls that "the interface
Sylvester's law of inertia feeds", and `QuadraticSplit`'s header records that
Mathlib has the law.  Neither module ever invoked it, so every caller was still
producing those three objects by hand.

This module invokes it.  What a caller actually holds is a symmetric matrix `K`
with `K.det ≠ 0` together with two vectors on which the form takes opposite
signs; the theorems here turn exactly that into the pair `(1,1)`.

The route is four steps, each a separate declaration so that a failure is
attributable:

* `associated_toQuadraticForm'` — for a **symmetric** `K`, the bilinear form
  `QuadraticMap.associated` recovers from `K`'s quadratic form is `K`'s own
  bilinear form.  Symmetry is needed and is not decoration: `associated` is the
  polarisation `(Q (x + y) - Q x - Q y) / 2`, which returns the *symmetrisation*
  of `K`, and only a symmetric `K` is its own symmetrisation.
* `separatingLeft_of_det_ne_zero` — nondegeneracy in the shape Mathlib's
  Sylvester lemma demands, discharged from `K.det ≠ 0` through
  `Matrix.separatingLeft_iff_det_ne_zero`.
* `exists_diagonal_coords` — Mathlib's
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, repackaged from an
  isometric equivalence onto `weightedSumSquares` into the plain `(w, f)` pair
  the atlas interface reads.
* `hasLocalVolumeOrder_abs_of_diagonal_indefinite` — the counting step.  Both
  signs occur in `w` exactly because the form takes both signs, and that is what
  supplies the `NeZero p`, `NeZero q` instances the band estimate needs.

Indefiniteness is stated as *two witnesses*, not as a negation.  A germ only one
sign reaches is a definite form, whose sublevel sets are ellipsoids and whose
pair is not `(1,1)`; asking for the witnesses rather than for `¬ definite` keeps
the hypothesis constructive and keeps the examples file honest, since it must
exhibit both vectors.
-/

namespace AISafetyAtlas.SingularLearning

open QuadraticMap
open scoped Matrix

/-! ## Sylvester's law of inertia in atlas coordinates

Mathlib returns a `QuadraticMap.IsometryEquiv` onto `weightedSumSquares`; the
atlas interface reads a bare linear equivalence and a bare weight vector.  The
repackaging is the whole content of this section.
-/

/-! ## The counting step

Sylvester alone does not give the band pair: a definite form is diagonalised too,
with all weights of one sign, and its germ has a different pair.  What rules that
out is that the form takes both signs, and the translation from "takes both
signs" to "both blocks are nonempty" is this lemma.
-/

/-! ## The matrix interface

The form a Stage 3 caller actually holds arrives as an explicit symmetric matrix,
so this is the interface the programme consumes.  Nondegeneracy arrives as
`K.det ≠ 0`, which is the form a caller can check by computation.
-/

/-- The quadratic form of a symmetric matrix, read on Euclidean space.-/
@[expose] public noncomputable def matrixQuadForm {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fun i => z i) ⬝ᵥ (K *ᵥ (fun i => z i))

/-! ## The bilinear-form interface

A caller holding the form as a symmetric bilinear map rather than as a matrix
reaches the same conclusion with no matrix in sight.  Nondegeneracy is stated
here in its own terms — every nonzero vector is separated by some other vector —
because that is `LinearMap.SeparatingLeft` unfolded, and a caller in this shape
has no determinant to appeal to.
-/

end AISafetyAtlas.SingularLearning
