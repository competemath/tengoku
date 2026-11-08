module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O70Proof
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O77
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.HessianBlock
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.LossExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O77(a) — conditional verification

This module proves the issue #12 fiber table by the exact reuse the candidate
claims: exchange the input and output dimension names and apply the O70
order-level theorem.  Centering at a factorization is proved to recover the
nonnegative loss, and the generic strict/weak bridge supplies A7's printed
strict band.  The only unproved binder is `EigenvalueLawStatement`.  Neither
`O70ExactLocalPairsExist` nor `O70ZetaPoleBridge` is used.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-! ## Criticality of a rung point

O77(b) is not proved in this module; `O77Chart.lean` proves it, as
`o77AllSaddlesHavePairOne_holds`, and consumes this section.  What is proved
here is the one fact the full-space loss expansion needs from the source
predicate: a rung point is a critical point of the loss.

The two equations are the matrix form of "the residual is orthogonal to every
first-order motion of the product".  They are consequences of the annihilation
clauses already inside `IsO77SaddleRungPoint`, not extra hypotheses: at a rung
point the residual is supported on the discarded modes, and those are exactly
the directions `A` and `Bᵀ` kill.
-/

open AISafetyAtlas.SingularLearning Matrix

/-- The rank-one rows of the spectral expansion, at the matrix type.-/
@[expose] public noncomputable def O77SpectralFrame.row {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (i : Fin r) : Matrix (Fin N) (Fin M) ℝ :=
  vecMulVec (frame.singularValue i • frame.leftMode i) (frame.rightMode i)

/-! ### The residual is supported on the discarded modes

The two criticality equations are the case `C = B`, `Z = A` of a single fact:
*anything* that kills every discarded left mode annihilates the residual from
the left, and anything that kills every discarded right mode annihilates it from
the right.  Stating it that way is what lets the same lemma serve the Hessian's
null space below, where the annihilating matrices are a variation `(X, Y)` and
not the point itself.
-/

/-! ### The Hessian at a rung point, and its null space

The exact expansion leaves `frobeniusSq (BX + YA) + 2⟨R, YX⟩` as the quadratic
part.  Whether MAIS-O77(b) is a Morse–Bott statement or a genuine
Gromoll–Meyer splitting turns on one question about that form: is its null space
exactly the tangent space of the rung set `C_k`?

If it is, the degenerate directions are tangent to a manifold along which the
loss is *constant* — the loss sees `(A, B)` only through `B * A`, and `B * A` is
frozen on `C_k` — so they are free in the sense of print's Lemma 6.4(ii), and no
splitting is needed at all.  Numerical evidence at both special and generic rung
points says the two spaces coincide.  This section proves the inclusion that
holds unconditionally; the reverse inclusion is where the frame's orthonormality
and the distinctness of the singular values have to enter, and it is not proved
here.
-/

/-- **The Hessian quadratic form of the O77 loss at a point**: the second-order
part of `L(A + X, B + Y) - L(A, B)`, read off `frobeniusSq_full_variation_of_critical`.
The cubic `2⟨BX + YA, YX⟩` and quartic `‖YX‖²` are dropped; the term `2⟨R, YX⟩`
is kept because it is second order in the variation, and it is the term through
which the discarded modes enter.-/
@[expose] public noncomputable def o77HessianForm {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  frobeniusSq (B * X + Y * A) + 2 * froIP (B * A - frame.target) (Y * X)

/-- The polar form of `o77HessianForm`.  Its diagonal is the quadratic form
(`o77HessianPolar_self`), which is what makes "null space" mean what it should.-/
@[expose] public noncomputable def o77HessianPolar {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) (X' : Matrix (Fin H) (Fin M) ℝ)
    (Y' : Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  froIP (B * X + Y * A) (B * X' + Y' * A)
    + froIP (B * A - frame.target) (Y * X' + Y' * X)

public theorem o77HessianPolar_self {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    o77HessianPolar frame A B X Y X Y = o77HessianForm frame A B X Y := by
  rw [o77HessianPolar, o77HessianForm, ← froIP_self (B * X + Y * A),
    froIP_add_right (B * A - frame.target) (Y * X) (Y * X)]
  ring

/-- **The tangent space of the rung set `C_k` at a rung point.**  `C_k` is cut out
by `B * A = truncation k` together with the two annihilation clauses, so a
variation is tangent to it when it kills each defining equation to first order.-/
@[expose] public def IsO77RungTangent {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (k : ℕ) (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) : Prop :=
  B * X + Y * A = 0 ∧
    (∀ i : Fin r, k ≤ (i : ℕ) → X *ᵥ frame.rightMode i = 0) ∧
    (∀ i : Fin r, k ≤ (i : ℕ) → Yᵀ *ᵥ frame.leftMode i = 0)

/-! ### The converse inclusion

The null space is characterised by two matrix equations, one for each half of the
variation.  They are the statement that the derivative of the quadratic form
vanishes in the `X` and the `Y` directions separately, written without the test
matrix by nondegeneracy of the Frobenius pairing.
-/

/-! ### The spectral step

`(BA)ᵀ(BA)` at a rung point is the truncation's Gram matrix, whose only nonzero
eigenvalues are the *kept* squared singular values.  A discarded one is different
from all of them — that is what the printed strict decrease is for — so nothing
is an eigenvector for it.  The two lemmas below are that computation, and they
are where `singularValue_strict` finally does work.
-/

/-! ### The null space is no larger than the tangent space -/

/-! ### The saddle direction

Pair `(1,1)` needs the transverse form to be *indefinite*: a definite
nondegenerate form in `D'` variables has pair `(D'/2, 1)`.  Nondegeneracy
transverse to `C_k` is what the Morse–Bott theorem above gives, so what is left is
that both signs occur.

There is a clean witness whenever some `c ≠ 0` is killed by `B` and by `Aᵀ`: the
variation `X = c v_kᵀ`, `Y = ± s_k u_k cᵀ` leaves the product fixed to first order
and picks up the first *discarded* mode at second order, so the whole Hessian is
the residual term and it is `∓ 2 s_k² ‖c‖²`.  That is the printed saddle
direction — descending it is exactly fitting one more singular mode.

At rung points where `ker B ∩ ker Aᵀ` is trivial, which numerically is the
generic case, this witness gives nothing. That case is settled by
`o77HessianForm_indefinite_of_rung` below, on a wider two-parameter block, and
needs no hypothesis print does not supply.
-/

/-- The saddle variation attached to a vector `c` and the first discarded mode.-/
@[expose] public noncomputable def saddleVariation {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) (hk : k < r) (c : Fin H → ℝ) (t : ℝ) :
    Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ :=
  (vecMulVec c (frame.rightMode ⟨k, hk⟩),
    vecMulVec ((t * frame.singularValue ⟨k, hk⟩) • frame.leftMode ⟨k, hk⟩) c)

/-! ### Indefiniteness at every rung, unconditionally

The theorem above needs a vector killed by both `B` and `Aᵀ`, which is not
available at a general rung point. The candidate's own argument does not need
one, and this section transcribes it.

It works on the wider two-parameter block `Ẋ = x v_αᵀ`, `Ẏ = u_α yᵀ`, where the
earlier `saddleVariation` tied the two factors to one vector. On that block the
Hessian is `xᵀ(BᵀB)x + yᵀ(AAᵀ)y − 2 s_α ⟨x, y⟩`: both diagonal terms are Gram
forms, hence positive semidefinite, and the coupling carries the sign. The block
is positive at `(z, −z)` for every nonzero `z`. It is negative at `(z, t z)` for
small `t > 0` whenever `B z = 0`, and at `(t z, z)` whenever `Aᵀ z = 0` — and one
of those kernels is nonzero at every rung, because otherwise `rank (B * A)` would
be `H`, against `rank (B * A) = k < r < H`.
-/

/-- The two-parameter variation block attached to a discarded mode: `x` enters
through the right mode and `y` through the left, independently.-/
@[expose] public noncomputable def o77BlockVariation {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) (x y : Fin H → ℝ) :
    Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ :=
  (vecMulVec x (frame.rightMode α), vecMulVec (frame.leftMode α) y)

/-! ## The loss as a smooth function, for the splitting step

Everything above is matrix algebra: exact identities in the entries, with no
derivative taken. The splitting print invokes next is a statement about a smooth
function and its Hessian, so it needs the loss presented that way. These two
lemmas are the whole bridge, and both are inherited: the O70 layer already
proved the reduced-rank loss real-analytic at every point of the coordinate
space, and O77's loss is that function with the two ambient dimensions
exchanged. -/

open scoped ContDiff

/-! ## The variation block as a subspace

Print calls `Adot = x v_α^T`, `Bdot = u_α y^T` "the `2H`-dimensional
variation block" and then treats it as the space the splitting's quadratic form
lives on. To be that, it has to be a subspace of the parameter space of
dimension `2H`. `o77BlockVariation_injective` is half of it; packaging the
parametrisation as a linear map supplies the rest. -/

/-- Print's variation block, as a linear map from `ℝ^H × ℝ^H` into the parameter
space. The map is linear because `vecMulVec` is linear in each argument
separately and each factor of the block varies only one of them.-/
@[expose] public noncomputable def o77BlockMap {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    ((Fin H → ℝ) × (Fin H → ℝ)) →ₗ[ℝ]
      (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) where
  toFun p := o77BlockVariation frame α p.1 p.2
  map_add' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    simp only [o77BlockVariation, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext i j; simp [Matrix.vecMulVec_apply, add_mul]
    · ext i j; simp [Matrix.vecMulVec_apply, mul_add]
  map_smul' := by
    rintro c ⟨x, y⟩
    simp only [o77BlockVariation, Prod.smul_mk, RingHom.id_apply, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext i j; simp [Matrix.vecMulVec_apply, mul_assoc]
    · ext i j; simp [Matrix.vecMulVec_apply]; ring

@[simp] public theorem o77BlockMap_apply {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) (x y : Fin H → ℝ) :
    o77BlockMap frame α (x, y) = o77BlockVariation frame α x y := rfl

/-! ## Print's spectral condition, discharged

`SingularLearning.det_hessianBlock_ne_zero` proves `K_α` nonsingular *given*
`det (P R - s_α^2 I) ≠ 0`, and until now nothing in this tree supplied that
hypothesis anywhere except at the trivial rank-zero rung, where both diagonal
blocks vanish. Print supplies it in one sentence:

> The nonzero eigenvalues of `QP` are those of `A^T B^T B A = (BA)^T (BA)`,
> namely `s_1^2, ..., s_k^2`. Since the target singular values are distinct and
> `α > k`, `s_α^2` is neither zero nor one of these eigenvalues.

The transcription below takes that route and needs no spectral theorem. What is
used is only that `s_α^2` is not an eigenvalue of `(BA)^T (BA)`, and at a
rung point `BA` is the ordered truncation, whose Gram operator acts on the kept
right modes by `s_i^2` and annihilates everything orthogonal to them. Pairing
the eigenvector equation with one kept right mode gives
`(s_j^2 - s_α^2)(v_j . y) = 0` with `s_j > s_α > 0`, so every such
coordinate vanishes, so the truncation kills `y` outright, so `y` is zero. -/

/-- Print's variation block as a subspace of the **Euclidean** parameter space,
which is where the volume interface lives.-/
@[expose] public noncomputable def o77BlockSubspace {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (H * M + N * H))) :=
  LinearMap.range ((matrixPairEquiv N M H).toLinearMap.comp (o77BlockMap frame α))

/-! ## The rung predicate is print's critical set, not a narrowing of it

Print fixes `w = (A, B) ∈ C_k` and then says "the defining criticality
conditions give `A v_α = 0`, `B^T u_α = 0`". The atlas's
`IsO77SaddleRungPoint` lists those two annihilation clauses among its
conjuncts rather than deriving them, and until now only the **forward**
direction was proved: `rung_transpose_mul_residual` and
`rung_residual_mul_transpose` show the clauses imply the two normal equations.

That left a scope question open in the direction that matters. If the clauses
were strictly stronger than criticality-plus-membership, then every theorem
quantified over `IsO77SaddleRungPoint` would range over a **subset** of print's
`C_k`, and an all-saddle claim proved of it would not be print's claim. The
converse below closes that: at a point where `B A` is the ordered truncation,
the two normal equations force the annihilation clauses, because the residual
reads off each discarded mode with a nonzero coefficient.
-/

end AISafetyAtlas.Conjectures.MAIS
