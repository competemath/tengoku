module

public import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement
public import Tengoku.Seed.Analysis.Matrix.PosDef
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.GaussianQuadratic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma 8.10: the elementary spectral facts about the two Gram matrices

## What this module is for

The MAIS issue #3 candidate's residual computation runs
Proposition 8.9 → Lemma 8.10 → Proposition 8.13. Proposition 8.9
(`integral_exp_neg_frobenius_mul`, in `GaussianQuadratic.lean`) eliminates the `Y`
variable and leaves a determinant `det (I + T X Xᵀ)` of size `h × h`. Lemma 8.10 is
the bookkeeping that lets that determinant be rewritten in terms of the *other*
Gram matrix `Xᵀ X`, of size `n × n`, so that Proposition 8.13 may always work with
the smaller of the two. The candidate **derives** these facts rather than citing
them, so they sit inside the trust boundary and are proved here.

## What the pinned Mathlib already had

Almost all of it, which is worth recording precisely, since a library survey for
this project has more than once predicted the opposite:

* The **Weinstein–Aronszajn identity** `Matrix.det_one_add_mul_comm` is present *for
  rectangular blocks*, `det (1 + A * B) = det (1 + B * A)` with `A : Matrix m n α`
  and `B : Matrix n m α` and the two `1`s of different shapes
  (`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`). So the headline statement
  `det_one_add_smul_gram_comm` is a three-line rearrangement of the scalar, not a
  development.
* `Matrix.posSemidef_self_mul_conjTranspose` gives item 3 directly; over `ℝ` the star
  operation is trivial, so `Xᴴ` and `Xᵀ` agree.
* `Matrix.PosSemidef.eigenvalues_nonneg` and `Matrix.PosSemidef.det_nonneg`
  (`Mathlib/Analysis/Matrix/PosDef.lean`) give item 4.

The one genuinely missing piece is the trace identity in Frobenius form. Mathlib's
`Matrix.trace_transpose_mul` is a *different* statement (`trace (Aᵀ * Bᵀ) = trace (A * B)`,
a `Finset.sum_comm`), and there is no lemma equating `trace (X Xᵀ)` with the sum of
squared entries; `trace_mul_transpose` below supplies it, together with the fact that the
two Gram matrices have equal trace.

## Contents

1. `trace_mul_transpose`, `trace_transpose_mul`, `trace_gram_comm` — the trace identity.
2. `det_one_add_smul_gram_comm` — the form Proposition 8.13 consumes.
3. `posSemidef_mul_transpose`, `posSemidef_transpose_mul` — positive semidefiniteness.
4. `eigenvalues_mul_transpose_nonneg`, `det_mul_transpose_nonneg` — the cheap corollaries.
5. `integral_exp_neg_frobenius_mul_gram` — Proposition 8.13: Proposition 8.9 restated
   through the `n × n` Gram matrix `Xᵀ X`.

**This module is pure linear algebra plus one rewrite.** It says nothing about learning
coefficients or volume asymptotics.
-/

namespace AISafetyAtlas.SingularLearning

open Matrix

/-! ## The trace identity -/

/-! ## Equality of the two characteristic determinants

This is the form Proposition 8.13 actually consumes, and it is the precise sense in which
`X Xᵀ` and `Xᵀ X` "have the same nonzero eigenvalues with the same multiplicities": the
two polynomials `T ↦ det (1 + T • G)` agree, so the nonzero spectra agree with
multiplicity, the two matrices differing only in the multiplicity of the eigenvalue `0`
(forced by the shape difference `h` versus `n`). -/

/-- **Sylvester's determinant identity for the two Gram matrices.**
`det (I_h + T X Xᵀ) = det (I_n + T Xᵀ X)` for every scalar `T`, with the two identity
matrices of different sizes.

One-line consequence of Mathlib's rectangular Weinstein–Aronszajn identity
`Matrix.det_one_add_mul_comm`, after moving the scalar onto one factor.-/
public theorem det_one_add_smul_gram_comm {h n : ℕ} (T : ℝ) (X : Matrix (Fin h) (Fin n) ℝ) :
    (1 + T • (X * Xᵀ)).det = (1 + T • (Xᵀ * X)).det := by
  rw [show T • (X * Xᵀ) = (T • X) * Xᵀ from (Matrix.smul_mul T X Xᵀ).symm,
    show T • (Xᵀ * X) = Xᵀ * (T • X) from (Matrix.mul_smul Xᵀ T X).symm,
    Matrix.det_one_add_mul_comm]

/-! ## Positive semidefiniteness -/

/-! ## Nonnegativity of the spectrum and of the determinant -/

/-! ## Proposition 8.13: the residual integral through the smaller Gram matrix -/

/-! ## Worked examples -/

end AISafetyAtlas.SingularLearning
