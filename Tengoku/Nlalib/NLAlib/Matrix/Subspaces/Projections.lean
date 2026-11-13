import Tengoku.Seed.LinearAlgebra.Matrix.Rank
import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Orthonormal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Orthonormal frames, projectors and residuals

Stated over `{𝕜 : Type*} [RCLike 𝕜]` with `conjTranspose` (RCLike round, decision D4); at
`𝕜 := ℝ` every definition is definitionally the old real one.

* `NLAlib.HasOrthonormalCols Q`: `Qᴴ Q = I` (at `ℝ`: `Qᵀ Q = I`).
* `NLAlib.projResidual Q A = A − Q (Qᴴ A) = (I − QQᴴ) A`, the part of `A` outside `range Q`.
* `NLAlib.IsBestFrobRankApprox A k Y`: `Y` has rank `≤ k` and minimises the Frobenius distance
  to `A` among rank-`≤ k` matrices (the Frobenius-norm optimality property of `⟦A⟧ₖ`; the
  truncated SVD attains it, `Matrix/Spectral/EckartYoung.lean`).

## Contents

* Isometry: `‖Qx‖² = ‖x‖²` for `Q` with orthonormal columns.
* The orthogonal projector `P = QQᴴ`: idempotence, `Qᴴ(I − P) = 0`.
* The residual: `projResidual Q A = (I − QQᴴ) A`, orthogonality to `range Q`, Pythagoras
  `‖A‖_F² = ‖QQᴴA‖_F² + ‖(I − QQᴴ)A‖_F²`, `‖(I − QQᴴ)A‖_F ≤ ‖A‖_F`, `‖QᴴA‖_F ≤ ‖A‖_F`.
* Best approximation in a range: `‖A − QB‖_F² = ‖(I − QQᴴ)A‖_F² + ‖QᴴA − B‖_F²`, and the
  monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case).
* Range-finder fact: `range(AΩ) ⊆ range(Q)` (written `Q (Qᴴ (A Ω)) = A Ω`) gives
  `(I − QQᴴ) A Ω = 0`.
* Unitary completions: a matrix with orthonormal columns has at most as many columns as
  rows (`card_le_card_of_hasOrthonormalCols`) and extends to a unitary matrix on any finite
  row type (`exists_unitary_completion`) or, with the complementary block, to
  `QQᴴ + Q⊥Q⊥ᴴ = I` (`exists_unitary_complement`, `Q⊥` with `card m − card q` columns); for
  such a completion `QᴴQ⊥ = 0` and `(I − QQᴴ)A = Q⊥Q⊥ᴴ(I − QQᴴ)A`.
* Vectors and compressions: `QQᴴx = x` on `range Q`, `‖Qᴴx‖² ≤ ‖x‖²` (equality on `range Q`),
  `Q'Q'ᴴQ = Q` under range inclusion, `QQᴴ = Q'Q'ᴴ` for equal ranges. (The compression `QᴴAQ`
  of a Hermitian `A` is Hermitian: Mathlib's `Matrix.isHermitian_conjTranspose_mul_mul`.)

## Real statements

Every statement is written with `ᴴ` and `star`. Over `ℝ` the `@[simp]` lemmas
`Matrix.conjTranspose_eq_transpose_of_trivial` and `star_trivial` turn them into the `ᵀ` /
plain dot-product forms; e.g. `rw [projResidual, Matrix.conjTranspose_eq_transpose_of_trivial]`
unfolds a real projResidual, and `rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
hQ.conjTranspose_mul_self]` rewrites `Qᵀ * Q` to `1`.

The canonical orthonormal basis matrix `orthonormalBasisMatrix S` of a subspace is in
`Matrix/Subspaces/OrthonormalBasisMatrix.lean`; the projector onto the range of an arbitrary
matrix is `rangeProjector` (`Matrix/Subspaces/RangeProjector.lean`).

Sources: Golub–Van Loan 2013, §2.4 and §5.4; Stewart–Sun 1990, §I.5; HMT 2011, §8.4 and §9.
Atlas: `projection-facts`, `eckart-young`, `orthonormal-completion`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-! ### Definitions -/

/-- `Y` is a **best rank-`k` approximation of `A` in the Frobenius norm**: `rank Y ≤ k` and
`‖A − Y‖_F ≤ ‖A − Z‖_F` for every `Z` of rank at most `k`. Golub–Van Loan 2013, Thm 2.4.8
(Eckart–Young); HMT 2011, §2.1.
atlas: best-rank-approx-def-/
def IsBestFrobRankApprox (A : Matrix m n 𝕜) (k : ℕ) (Y : Matrix m n 𝕜) : Prop :=
  Y.rank ≤ k ∧ ∀ Z : Matrix m n 𝕜, Z.rank ≤ k → frobSq (A - Y) ≤ frobSq (A - Z)

/-! ### Isometry -/

/-- If `U` has orthonormal columns then `‖Ux‖² = ‖x‖²`, written with dot products.
Golub–Van Loan 2013, §2.4; atlas `projection-facts`.
@isnad1 id=eq.1h5v.s8.1841d8c7b411 from=translated src=- shape=44c1f400 vocab=f6dae9ec
-/
theorem star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols [DecidableEq q]
    {U : Matrix m q 𝕜} (hU : HasOrthonormalCols U) (x : q → 𝕜) :
    star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
  rw [star_mulVec_dotProduct_mulVec_self, hU.conjTranspose_mul_self, Matrix.one_mulVec]

/-! ### The orthogonal projector `QQᴴ` -/

/-- Idempotence of `P = QQᴴ` for `Q` with orthonormal columns: `P² = P`.
Atlas `projection-facts`.
@isnad1 id=eq.1h4v.s8.bbe24b665ddd from=translated src=- shape=b5ae1cce vocab=1105a194
-/
theorem mul_conjTranspose_mul_mul_conjTranspose [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : Q * Qᴴ * (Q * Qᴴ) = Q * Qᴴ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul]

/-- Idempotence of the complementary projector `I − QQᴴ`. Atlas `projection-facts`.
@isnad1 id=eq.1h4v.s9.395f4212c3bf from=translated src=- shape=8e31e747 vocab=2ee96319
-/
theorem one_sub_mul_conjTranspose_idem [DecidableEq m] [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᴴ) * (1 - Q * Qᴴ) = 1 - Q * Qᴴ := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, mul_conjTranspose_mul_mul_conjTranspose hQ]
  abel

/-- `Qᴴ (I − QQᴴ) = 0` for `Q` with orthonormal columns. Atlas `projection-facts`.
@isnad1 id=eq.1h4v.s8.da8216406c7b from=translated src=- shape=2d871faa vocab=2ee96319
-/
theorem conjTranspose_mul_one_sub_mul_conjTranspose [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) : Qᴴ * (1 - Q * Qᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQ.conjTranspose_mul_self,
    Matrix.one_mul, sub_self]

/-- `(I − QQᴴ)ᴴ Q = 0` for `Q` with orthonormal columns. Atlas `projection-facts`.
@isnad1 id=eq.1h4v.s8.ee0a1fafcf98 from=translated src=- shape=eb940cbc vocab=2ee96319
-/
theorem one_sub_mul_conjTranspose_conjTranspose_mul [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) : (1 - Q * Qᴴ)ᴴ * Q = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    hQ.conjTranspose_mul_self, Matrix.mul_one, sub_self]

/-! ### The residual `(I − QQᴴ) A` -/

omit [Fintype n] in
/-- `projResidual Q A = (I − QQᴴ) A`. Atlas `projection-facts`.
@isnad1 id=eq.0h6v.s8.1b5152b48f96 from=translated src=- shape=8bf8a22b vocab=364a4384
-/
theorem residual_eq_one_sub_mul [DecidableEq m] (Q : Matrix m q 𝕜)
    (A : Matrix m n 𝕜) : projResidual Q A = (1 - Q * Qᴴ) * A := by
  rw [projResidual, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [Fintype n] in
/-- Orthogonal decomposition `A = Q(QᴴA) + projResidual Q A`. Atlas `projection-facts`.
@isnad1 id=eq.0h6v.s7.8ffbd0a9a7e6 from=translated src=- shape=586f2fff vocab=76839f4d
-/
theorem mul_conjTranspose_mul_add_residual (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) :
    Q * (Qᴴ * A) + projResidual Q A = A := by
  rw [projResidual]; abel

omit [Fintype n] in
/-- The residual is orthogonal to `range Q`: `Qᴴ (I − QQᴴ) A = 0`. Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=eq.1h6v.s7.21d8a73d7761 from=translated src=- shape=58eff1bf vocab=96ff7732
-/
theorem conjTranspose_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : Qᴴ * projResidual Q A = 0 := by
  rw [projResidual, Matrix.mul_sub, ← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul,
    sub_self]

/-- The residual is Frobenius-orthogonal to every matrix `QX` with columns in `range Q`.
Atlas `projection-facts`.
@isnad1 id=eq.1h7v.s6.96ba197c0fc3 from=translated src=- shape=6a83b95e vocab=cbf55bc7
-/
theorem frobInner_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (X : Matrix q n 𝕜) (A : Matrix m n 𝕜) : frobInner (Q * X) (projResidual Q A) = 0 := by
  rw [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    conjTranspose_mul_residual hQ, Matrix.mul_zero, Matrix.trace_zero, map_zero]

omit [Fintype n] in
/-- Projecting the residual again changes nothing: `(I − QQᴴ)² A = (I − QQᴴ) A`.
Atlas `projection-facts`.
@isnad1 id=eq.1h6v.s6.e36e09473e33 from=translated src=- shape=453bc2dc vocab=87c100c9
-/
theorem residual_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : projResidual Q (projResidual Q A) = projResidual Q A := by
  show projResidual Q A - Q * (Qᴴ * projResidual Q A) = projResidual Q A
  rw [conjTranspose_mul_residual hQ, Matrix.mul_zero, sub_zero]

/-- The residual of `QX` vanishes. Atlas `projection-facts`.
@isnad1 id=eq.1h6v.s7.102ecc9b62ae from=translated src=- shape=cbc810c6 vocab=a3ef9e38
-/
theorem residual_mul_self [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    {p : Type*} [Fintype p] (X : Matrix q p 𝕜) : projResidual Q (Q * X) = 0 := by
  rw [projResidual, ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul, sub_self]

/-- The residual commutes with right multiplication: `((I − QQᴴ)A) Ω = (I − QQᴴ)(AΩ)`.
Atlas `projection-facts`.
@isnad1 id=eq.0h8v.s7.8ccd24595b7b from=translated src=- shape=169a8bc0 vocab=6a76b3f8
-/
theorem residual_mul (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) {p : Type*} [Fintype p]
    (Ω : Matrix n p 𝕜) : projResidual Q A * Ω = projResidual Q (A * Ω) := by
  simp only [projResidual, Matrix.sub_mul, Matrix.mul_assoc]

/-- If `range(AΩ) ⊆ range(Q)`, written `Q (Qᴴ (AΩ)) = AΩ`, then `(I − QQᴴ) A Ω = 0`.
This is how `Q = orth(AΩ)` enters the range-finder analysis (HMT 2011, proof of Thm 9.1).
No orthonormality is needed. Over `ℝ` the hypothesis may be given as `Q (Qᵀ (AΩ)) = AΩ`.
Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=eq.1h8v.s8.676a2eb1d43e from=translated src=- shape=3a1bf967 vocab=a2bc5b20
-/
theorem residual_mul_eq_zero_of_range {Q : Matrix m q 𝕜} {A : Matrix m n 𝕜} {p : Type*}
    [Fintype p] {Ω : Matrix n p 𝕜} (h : Q * (Qᴴ * (A * Ω)) = A * Ω) :
    projResidual Q A * Ω = 0 := by
  rw [residual_mul, projResidual, h, sub_self]

/-! ### Pythagoras and contraction -/

/-- The squared Frobenius size of an orthonormal frame is its width.
Stewart–Sun §I.5; valid at width zero.
@isnad1 id=eq.1h4v.s5.22bfb81d2910 from=translated src=- shape=1f41c7a6 vocab=2a897624
-/
theorem frobSq_frame_eq_card [DecidableEq n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    frobSq Q = Fintype.card n := by
  rw [frobSq, frobInner_eq_trace, hQ.conjTranspose_mul_self, Matrix.trace_one,
    RCLike.natCast_re]

/-- Pythagoras for the projector: `‖A‖_F² = ‖Q(QᴴA)‖_F² + ‖(I − QQᴴ)A‖_F²`.
Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=eq.1h6v.s7.9982c2adfcc2 from=translated src=- shape=d8c584e7 vocab=48072da1
-/
theorem frobSq_eq_frobSq_proj_add_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq A = frobSq (Q * (Qᴴ * A)) + frobSq (projResidual Q A) := by
  conv_lhs => rw [← mul_conjTranspose_mul_add_residual Q A]
  exact frobSq_add_of_frobInner_eq_zero _ _ (frobInner_mul_residual hQ _ A)

/-- Pythagoras with the projection measured in `range Q` coordinates:
`‖A‖_F² = ‖QᴴA‖_F² + ‖(I − QQᴴ)A‖_F²`. Atlas `projection-facts`.
@isnad1 id=eq.1h6v.s7.e215f9e81f6d from=translated src=- shape=2b21b252 vocab=48072da1
-/
theorem frobSq_eq_frobSq_conjTranspose_mul_add_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq A = frobSq (Qᴴ * A) + frobSq (projResidual Q A) := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A,
    frobSq_mul_left_of_orthonormal hQ.conjTranspose_mul_self]

/-- `‖(I − QQᴴ)A‖_F² = ‖A‖_F² − ‖QᴴA‖_F²`. Atlas `projection-facts`.
@isnad1 id=eq.1h6v.s7.d321ad66317c from=translated src=- shape=5e20da03 vocab=5b3518e5
-/
theorem frobSq_residual_eq_sub [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq (projResidual Q A) = frobSq A - frobSq (Qᴴ * A) := by
  rw [frobSq_eq_frobSq_conjTranspose_mul_add_residual hQ A]; ring

/-- The residual contracts: `‖(I − QQᴴ)A‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=le.1h6v.s6.e4f2297cc4ec from=translated src=- shape=9ab4374e vocab=707b349f
-/
theorem frobSq_residual_le [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : frobSq (projResidual Q A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A]
  exact le_add_of_nonneg_left (frobSq_nonneg _)

/-- `‖QᴴA‖_F² ≤ ‖A‖_F²` for `Q` with orthonormal columns. Atlas `projection-facts`.
@isnad1 id=le.1h6v.s7.6d7f19e1ab60 from=translated src=- shape=7d4abe2e vocab=052bcb1c
-/
theorem frobSq_conjTranspose_mul_le [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : frobSq (Qᴴ * A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_conjTranspose_mul_add_residual hQ A]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- The projection contracts: `‖QQᴴA‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`.
@isnad1 id=le.1h6v.s7.d83a18f20884 from=translated src=- shape=54f90aa7 vocab=052bcb1c
-/
theorem frobSq_proj_le [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : frobSq (Q * (Qᴴ * A)) ≤ frobSq A := by
  rw [frobSq_mul_left_of_orthonormal hQ.conjTranspose_mul_self]
  exact frobSq_conjTranspose_mul_le hQ A

/-! ### Best approximation in a range and monotonicity -/

/-- Pythagoras in `range Q`: for every `B`,
`‖A − QB‖_F² = ‖(I − QQᴴ)A‖_F² + ‖QᴴA − B‖_F²` (proof of HMT 2011, Thm 9.1).
Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=eq.1h7v.s8.8a7e08f01b8c from=translated src=- shape=19b9cf7b vocab=25344297
-/
theorem frobSq_sub_mul_eq [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix q n 𝕜) :
    frobSq (A - Q * B) = frobSq (projResidual Q A) + frobSq (Qᴴ * A - B) := by
  have hdecomp : A - Q * B = projResidual Q A + Q * (Qᴴ * A - B) := by
    rw [projResidual, Matrix.mul_sub]; abel
  rw [hdecomp, frobSq_add_of_frobInner_eq_zero _ _ (by
      rw [frobInner_comm]; exact frobInner_mul_residual hQ _ A),
    frobSq_mul_left_of_orthonormal hQ.conjTranspose_mul_self]

/-- `Q(QᴴA)` is the best Frobenius approximation of `A` with columns in `range Q`:
`‖(I − QQᴴ)A‖_F² ≤ ‖A − QB‖_F²` for every `B`. Atlas `projection-facts`.
@isnad1 id=le.1h7v.s7.18f0df4c7f58 from=translated src=- shape=117e357f vocab=24e4e101
-/
theorem frobSq_residual_le_frobSq_sub_mul [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix q n 𝕜) :
    frobSq (projResidual Q A) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq hQ A B]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- Monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case):
if `range Q₁ ⊆ range Q₂`, written `Q₁ = Q₂ C`, then `‖(I − Q₂Q₂ᴴ)A‖_F² ≤ ‖(I − Q₁Q₁ᴴ)A‖_F²`.
Deviation: only `Q₂` needs orthonormal columns; `Q₁` is arbitrary (with `residual` defined
by the formula `A − Q₁Q₁ᴴA`). Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=le.2h9v.s7.3bf39113bf2c from=translated src=- shape=92e8c500 vocab=f3a35f20
-/
theorem frobSq_residual_le_of_eq_mul [DecidableEq q] {q₁ : Type*} [Fintype q₁]
    {Q₁ : Matrix m q₁ 𝕜} {Q₂ : Matrix m q 𝕜} (hQ₂ : HasOrthonormalCols Q₂)
    {C : Matrix q q₁ 𝕜} (hC : Q₁ = Q₂ * C) (A : Matrix m n 𝕜) :
    frobSq (projResidual Q₂ A) ≤ frobSq (projResidual Q₁ A) := by
  have h : projResidual Q₁ A = A - Q₂ * (C * (Q₁ᴴ * A)) := by
    rw [projResidual, hC, Matrix.mul_assoc, ← hC]
  rw [h]
  exact frobSq_residual_le_frobSq_sub_mul hQ₂ A _

/-- `Q ⟦QᴴA⟧ₖ` is a best rank-`k` Frobenius approximation of `A` among matrices `QB` with
`rank B ≤ k` (HMT 2011, proof of Thm 9.1). Atlas `projection-facts`.
atlas: projection-facts
@isnad1 id=le.3h9v.s8.37b7b6a46b87 from=translated src=- shape=7a4f5693 vocab=1887d6f9
-/
theorem frobSq_sub_mul_le_of_isBestFrobRankApprox [DecidableEq q] {k : ℕ} {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n 𝕜} {Y : Matrix q n 𝕜}
    (hY : IsBestFrobRankApprox (Qᴴ * A) k Y) (B : Matrix q n 𝕜) (hB : B.rank ≤ k) :
    frobSq (A - Q * Y) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq hQ A Y,
    frobSq_sub_mul_eq hQ A B]
  exact add_le_add le_rfl (hY.2 B hB)

/-! ### Orthogonality of column blocks and orthogonal completions -/

omit [Fintype n] [Fintype q] in
/-- `AᴴB = 0 ↔ BᴴA = 0`: orthogonality of column spaces is symmetric.
Atlas `projection-facts`.
@isnad1 id=iff.0h6v.s8.d066950989bf from=translated src=- shape=c6fb723d vocab=87b3128b
-/
theorem conjTranspose_mul_eq_zero_comm {A : Matrix m n 𝕜} {B : Matrix m q 𝕜} :
    Aᴴ * B = 0 ↔ Bᴴ * A = 0 := by
  constructor <;> intro h <;> simpa using congrArg Matrix.conjTranspose h

omit [Fintype q] in
/-- `(PᴴQ)ᴴ(PᴴQ) = (QᴴP)(QᴴP)ᴴ`: the Gram matrix of `PᴴQ` is the outer Gram matrix of
`QᴴP`. Atlas `projection-facts`.
@isnad1 id=eq.0h6v.s9.82b789dee3ed from=translated src=- shape=33c77b03 vocab=87b3128b
-/
theorem gram_conjTranspose_mul_eq (P : Matrix m n 𝕜) (Q : Matrix m q 𝕜) :
    (Pᴴ * Q)ᴴ * (Pᴴ * Q) = (Qᴴ * P) * (Qᴴ * P)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- If `Q`, `Qp` have orthonormal columns and `QQᴴ + QpQpᴴ = I`, then `QᴴQp = 0`.
Golub–Van Loan 2013, §2.4; atlas `orthonormal-completion`.
@isnad1 id=eq.3h6v.s8.adfe4d19a700 from=translated src=- shape=12d3651b vocab=c92df3b4
-/
theorem conjTranspose_mul_eq_zero_of_completion [DecidableEq m] [DecidableEq n] [DecidableEq q]
    {Q : Matrix m q 𝕜} {Qp : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (hQp : HasOrthonormalCols Qp) (hcomp : Q * Qᴴ + Qp * Qpᴴ = 1) : Qᴴ * Qp = 0 := by
  have h := congrArg (fun M => Qᴴ * M * Qp) hcomp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] at h
  rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, hQp.conjTranspose_mul_self, Matrix.mul_one] at h
  simpa using h

omit [Fintype n] in
/-- For a completion `QQᴴ + QpQpᴴ = I` of `Q`, the residual lies in `range Qp`:
`(I − QQᴴ)A = Qp (Qpᴴ (I − QQᴴ)A)`. Golub–Van Loan 2013, §2.4; atlas `projection-facts`.
@isnad1 id=eq.2h8v.s9.88fb8f6e8038 from=translated src=- shape=f9339936 vocab=ac675ccb
-/
theorem residual_eq_mul_conjTranspose_mul_residual [DecidableEq m] [DecidableEq q] {r : Type*}
    [Fintype r] {Q : Matrix m q 𝕜} {Qp : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᴴ + Qp * Qpᴴ = 1) (A : Matrix m n 𝕜) :
    projResidual Q A = Qp * (Qpᴴ * projResidual Q A) := by
  have h : (Q * Qᴴ + Qp * Qpᴴ) * projResidual Q A = projResidual Q A := by
    rw [hcomp, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, conjTranspose_mul_residual hQ A,
    Matrix.mul_zero, zero_add] at h
  exact h.symm

/-- The column space `range B` of `B : Matrix m n 𝕜` as a subspace of `EuclideanSpace 𝕜 m`.-/
def columnSpace [DecidableEq n] (B : Matrix m n 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  LinearMap.range (Matrix.toEuclideanLin B)

/-- The column space is the span of the columns.
@isnad1 id=eq.0h4v.s8.673e86e0fb81 from=translated src=- shape=367cfc66 vocab=71979090
-/
theorem columnSpace_eq_span_columns [DecidableEq n] (B : Matrix m n 𝕜) :
    columnSpace B = Submodule.span 𝕜
      (Set.range (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace 𝕜 m))) := by
  change LinearMap.range (Matrix.toEuclideanLin B) = _
  rw [← Submodule.map_top, ← (EuclideanSpace.basisFun n 𝕜).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  have hf : (Matrix.toEuclideanLin B) ∘ (EuclideanSpace.basisFun n 𝕜).toBasis =
      (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace 𝕜 m)) := by
    funext j
    simp only [Function.comp_def, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_single]
    simp
  exact congrArg (Submodule.span 𝕜) (congrArg Set.range hf)

/-- Columns of a matrix as vectors of Euclidean space.-/
private def col {ι : Type*} (V : Matrix m ι 𝕜) (j : ι) : EuclideanSpace 𝕜 m :=
  WithLp.toLp 2 (fun i => V i j)

/-- A matrix has orthonormal columns exactly when its Euclidean columns form a
Mathlib `Orthonormal` family, over either the real or complex field.
@isnad1 id=iff.0h4v.s7.cab6203dc5c3 from=translated src=- shape=b48b3d8b vocab=3350d929
-/
theorem hasOrthonormalCols_iff_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix m ι 𝕜) :
    HasOrthonormalCols V ↔ Orthonormal 𝕜 (fun j => WithLp.toLp 2 (V.col j)) := by
  rw [orthonormal_iff_ite]
  constructor
  · intro hV a b
    have h := congrFun (congrFun hV.conjTranspose_mul_self a) b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.col_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  · intro hV
    ext a b
    have h := hV a b
    simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.col_apply] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

/-- The Euclidean columns of a matrix with orthonormal columns are a Mathlib
`Orthonormal` family.
@isnad1 id=orthonor.1h4v.s7.8ba451be2ab5 from=translated src=- shape=d9243ebd vocab=3350d929
-/
theorem HasOrthonormalCols.orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Matrix m ι 𝕜} (hV : HasOrthonormalCols V) :
    Orthonormal 𝕜 (fun j => WithLp.toLp 2 (V.col j)) :=
  (hasOrthonormalCols_iff_orthonormal V).mp hV

/-- A matrix with orthonormal columns has at most as many columns as rows (general finite
index types). Atlas `orthonormal-completion`.
atlas: orthonormal-completion
@isnad1 id=le.1h4v.s5.b55cb81e295a from=translated src=- shape=d5dbedcd vocab=447260c3
-/
theorem card_le_card_of_hasOrthonormalCols {r : Type*} [Fintype r] [DecidableEq r]
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q) : Fintype.card r ≤ Fintype.card m := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v => Qᴴ *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h
    rwa [hQ.conjTranspose_mul_self, Matrix.one_mulVec, Matrix.one_mulVec] at h
  simpa [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective hinj

/-- **Unitary completion.** A matrix `V` with orthonormal columns indexed by `ι`, placed in
the columns `e '' ι` of the finite row type `m`, extends to a unitary `m × m` matrix `W`
(`WᴴW = I`). Golub–Van Loan 2013, §2.4 (completion of an orthonormal set); HMT 2011, §10.2.
Atlas `orthonormal-completion`.
atlas: orthonormal-completion
@isnad1 id=ex.1h5v.s6.f416a7e206c6 from=translated src=- shape=e80cb1d7 vocab=3fdcc4cd
-/
theorem exists_unitary_completion [DecidableEq m] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix m ι 𝕜) (hV : HasOrthonormalCols V) (e : ι ↪ m) :
    ∃ W : Matrix m m 𝕜, HasOrthonormalCols W ∧ ∀ i j, W i (e j) = V i j := by
  classical
  let v : m → EuclideanSpace 𝕜 m := Function.extend e (col V) 0
  have hv : Orthonormal 𝕜 ((Set.range e).domRestrict v) := by
    have h1 : (Set.range e).domRestrict v =
        col V ∘ (Equiv.ofInjective e e.injective).symm := by
      funext x
      obtain ⟨a, j, rfl⟩ := x
      have : (Equiv.ofInjective e e.injective).symm ⟨e j, j, rfl⟩ = j :=
        (Equiv.ofInjective e e.injective).symm_apply_eq.mpr rfl
      simp only [Set.domRestrict_apply, Function.comp_apply, this, v]
      exact e.injective.extend_apply _ _ _
    rw [h1]
    exact (hV.orthonormal).comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])
  refine ⟨Matrix.of fun i a => b a i, ?_, ?_⟩
  · ext a c
    have := (orthonormal_iff_ite.mp b.orthonormal) a c
    simp only [PiLp.inner_apply, RCLike.inner_apply] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  · intro i j
    simp only [Matrix.of_apply]
    rw [hb (e j) ⟨j, rfl⟩]
    simp only [v, e.injective.extend_apply, col]

/-- **Unitary complement.** A matrix `Q : m × q` with orthonormal columns has a complement
`Qp` with `card m − card q` orthonormal columns and `QQᴴ + QpQpᴴ = I`. From
`exists_unitary_completion`. Golub–Van Loan 2013, §2.4; atlas `orthonormal-completion`.
atlas: orthonormal-completion
@isnad1 id=ex.1h4v.s8.2dd98ff991cb from=translated src=- shape=d9ef6d75 vocab=140832c8
-/
theorem exists_unitary_complement [DecidableEq m] [DecidableEq q] (Q : Matrix m q 𝕜)
    (hQ : HasOrthonormalCols Q) :
    ∃ Qp : Matrix m (Fin (Fintype.card m - Fintype.card q)) 𝕜,
      HasOrthonormalCols Qp ∧ Q * Qᴴ + Qp * Qpᴴ = 1 := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (card_le_card_of_hasOrthonormalCols hQ)
  obtain ⟨W, hW, hWQ⟩ := exists_unitary_completion Q hQ e
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW.conjTranspose_mul_self
  let s : Finset m := (Finset.univ.map e)ᶜ
  have hs : s.card = Fintype.card m - Fintype.card q := by
    simp [s, Finset.card_compl, Finset.card_map]
  let g : Fin (Fintype.card m - Fintype.card q) → m :=
    fun j => (s.equivFin.symm (Fin.cast hs.symm j)).1
  have hg : Function.Injective g := fun a b h => by
    have := s.equivFin.symm.injective (Subtype.ext h)
    simpa [Fin.ext_iff] using congrArg Fin.val this
  have hgs : ∀ j, g j ∈ s := fun j => (s.equivFin.symm _).2
  have hsum (F : m → 𝕜) : ∑ j, F (g j) = ∑ a ∈ s, F a := by
    rw [← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv ((finCongr hs.symm).trans s.equivFin.symm) _ _ fun j => rfl)
  refine ⟨Matrix.of fun i j => W i (g j), ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun hW.conjTranspose_mul_self (g a)) (g b)
    simpa [HasOrthonormalCols, Matrix.mul_apply, Matrix.one_apply, hg.eq_iff] using this
  · ext a b
    have := congrFun (congrFun hWW a) b
    rw [Matrix.mul_apply, ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [← this, hsum (fun c => W a c * star (W b c))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, Matrix.conjTranspose_apply]
    rw [← hWQ a j, ← hWQ b j]

/-! ### Projected matrices and vectors in a range -/

omit [Fintype m] in
/-- If `Q` has orthonormal columns and `x ∈ range Q`, then `Q Qᴴ x = x`: the projector `QQᴴ`
fixes its range. Atlas `projection-facts`.
@isnad1 id=eq.2h5v.s9.fecb08f361f7 from=translated src=- shape=5d4ad4b1 vocab=6c07bdbc
-/
theorem mulVec_conjTranspose_mulVec_of_mem_range [Fintype m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) {x : m → 𝕜}
    (hx : x ∈ LinearMap.range Q.mulVecLin) : Q *ᵥ (Qᴴ *ᵥ x) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h : Qᴴ *ᵥ (Q *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]
  simp only [Matrix.mulVecLin_apply, h]

/-- `Qᴴ` is a contraction for `Q` with orthonormal columns: `‖Qᴴ x‖² ≤ ‖x‖²` (Bessel), written
with explicit sums. Atlas `projection-facts`.
@isnad1 id=le.1h5v.s7.ab1e1f1aba50 from=translated src=- shape=74306c76 vocab=e09ed91b
-/
theorem sum_norm_sq_conjTranspose_mulVec_le [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (x : m → 𝕜) :
    ∑ i, ‖(Qᴴ *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  classical
  have hn : specNorm Qᴴ ≤ 1 := by
    rw [specNorm_conjTranspose]
    exact specNorm_le_one_of_orthonormal hQ.conjTranspose_mul_self
  have h := sum_norm_sq_mulVec_le_specNorm_sq Qᴴ x
  have h1 : specNorm Qᴴ ^ 2 ≤ 1 := by
    have := specNorm_nonneg Qᴴ
    nlinarith
  have h2 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

omit [Fintype m] in
/-- For `x ∈ range Q` and `Q` with orthonormal columns, `‖Qᴴ x‖² = ‖x‖²`, written with dot
products. Atlas `projection-facts`.
@isnad1 id=eq.2h5v.s9.ef019ae950ba from=translated src=- shape=f81b84ad vocab=c1e3ef07
-/
theorem star_conjTranspose_mulVec_dotProduct_self_of_mem_range [Fintype m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) {x : m → 𝕜}
    (hx : x ∈ LinearMap.range Q.mulVecLin) :
    star (Qᴴ *ᵥ x) ⬝ᵥ (Qᴴ *ᵥ x) = star x ⬝ᵥ x := by
  obtain ⟨y, rfl⟩ := hx
  have h : Qᴴ *ᵥ (Q *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]
  simp only [Matrix.mulVecLin_apply, h]
  exact (star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ y).symm

omit [Fintype m] in
/-- Range inclusion as a matrix identity: if `range Q ⊆ range Q'` and `Q'` has orthonormal
columns, then `Q' Q'ᴴ Q = Q`. Atlas `projection-facts`.
@isnad1 id=eq.2h6v.s9.8f0844a8372b from=translated src=- shape=824e640a vocab=3d232740
-/
theorem mul_conjTranspose_mul_eq_of_range_le [Fintype m] [DecidableEq q] {q' : Type*}
    [Fintype q'] {Q : Matrix m q' 𝕜} {Q' : Matrix m q 𝕜} (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin ≤ LinearMap.range Q'.mulVecLin) : Q' * (Q'ᴴ * Q) = Q := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact mulVec_conjTranspose_mulVec_of_mem_range hQ' (h ⟨v, rfl⟩)

omit [Fintype m] in
/-- The orthogonal projector depends only on the range: if `Q`, `Q'` have orthonormal columns
and the same range, then `QQᴴ = Q'Q'ᴴ`. Atlas `projection-facts`.
@isnad1 id=eq.3h6v.s9.0e90461b3df7 from=translated src=- shape=919c662c vocab=3b106c74
-/
theorem mul_conjTranspose_eq_of_range_eq [Fintype m] [DecidableEq q] {q' : Type*} [Fintype q']
    [DecidableEq q'] {Q : Matrix m q 𝕜} {Q' : Matrix m q' 𝕜} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin = LinearMap.range Q'.mulVecLin) : Q * Qᴴ = Q' * Q'ᴴ := by
  have h1 : Q' * (Q'ᴴ * Q) = Q := mul_conjTranspose_mul_eq_of_range_le hQ' h.le
  have h2 : Q * (Qᴴ * Q') = Q' := mul_conjTranspose_mul_eq_of_range_le hQ h.ge
  have e1 : Q * Qᴴ = Q' * Q'ᴴ * (Q * Qᴴ) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Q', h1]
  calc Q * Qᴴ = (Q * Qᴴ)ᴴ := (Matrix.isHermitian_mul_conjTranspose_self Q).symm
    _ = (Q' * Q'ᴴ * (Q * Qᴴ))ᴴ := by rw [← e1]
    _ = Q * (Qᴴ * Q') * Q'ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Q' * Q'ᴴ := by rw [h2]

end NLAlib
