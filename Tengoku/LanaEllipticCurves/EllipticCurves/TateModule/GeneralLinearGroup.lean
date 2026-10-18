/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.Algebra.Group.Units.Equiv
import Tengoku.Seed.LinearAlgebra.GeneralLinearGroup.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms of a free module as a matrix general linear group

A basis `b : Basis n R M` of a module over a commutative ring identifies the group of
`R`-linear automorphisms of `M` with the matrix general linear group:
$$ \operatorname{Aut}_R(M) \;\cong\; \mathrm{GL}_n(R). $$

Mathlib already has this equivalence, in the `GL → Aut` direction: compose
`Matrix.GeneralLinearGroup.toLin' b : GL n R ≃* (M →ₗ[R] M)ˣ` with
`LinearMap.GeneralLinearGroup.generalLinearEquiv : (M →ₗ[R] M)ˣ ≃* (M ≃ₗ[R] M)`. What this file
adds is the `Aut → GL` spelling, assembled instead from `LinearMap.toMatrixAlgEquiv`, the algebra
equivalence `(M →ₗ[R] M) ≃ₐ[R] Matrix n n R`, together with entry formulas for the matrix of an
automorphism *and of its inverse* — the latter has no counterpart in Mathlib, and entry formulas
are the only thing a consumer ever needs once the equivalence exists.

The two spellings agree, and are not left as unrelated definitions: `linearEquivMulEquivGL_symm`
below says that `b.linearEquivMulEquivGL.symm` **is** the Mathlib composite, for an arbitrary
basis of an arbitrary module over an arbitrary commutative ring. In particular the two conventions
differ by no transpose: both take column `j` of the matrix to be the coordinate vector of the
image of `b j`.

⚠️ **That statement used to be a scope limitation rather than a theorem**, and the sentence that
carried it read *"`EllipticCurves.TateModule.MatrixRepCompat` proves
`b.linearEquivMulEquivGL = (matrixAutEquivTwo b).symm` for the basis of `T₂E` that this
development actually uses"*. Neither side of the identity mentions a prime, a Tate module or a
curve, so there was nothing to restrict; the elliptic-curve readings are now corollaries, in
`EllipticCurves.TateModule.PrimaryMatrixRepCompat` at an arbitrary prime and in
`EllipticCurves.TateModule.MatrixRepCompat` / `EllipticCurves.TateModule.MatrixRepCompatThree`
at `ℓ = 2` and `ℓ = 3`.

There is nothing about elliptic curves here; the file is stated for an arbitrary commutative ring.

## Motivation

For an elliptic curve over a field `F` with `(2 : F) ≠ 0` and `F` algebraically closed, the
`2`-adic Tate module `T₂E` is free of rank two over `ℤ_[2]`
(`EllipticCurves.TateModule.Free`). Feeding a basis of it into `Basis.linearEquivMulEquivGL`
converts the abstract Galois representation `ρ_2 : G → Aut_{ℤ_2}(T₂E)` of
`EllipticCurves.TateModule.GaloisAction` into the classical matrix representation
`ρ_{E,2} : G → GL₂(ℤ_2)`. That representation lives in `EllipticCurves.TateModule.MatrixRep`,
which reaches `GL₂` along a different chain (`Matrix.GeneralLinearGroup.toLin'`);
`EllipticCurves.TateModule.PrimaryMatrixRepCompat` transports `linearEquivMulEquivGL_symm` to that
setting at an arbitrary prime, and `EllipticCurves.TateModule.MatrixRepCompat` and
`EllipticCurves.TateModule.MatrixRepCompatThree` read it off at `ℓ = 2` and `ℓ = 3`.

## Main definitions

* `Module.Basis.linearEquivMulEquivGL`: the multiplicative equivalence
  `(M ≃ₗ[R] M) ≃* GL n R` attached to a basis.

## Main statements

* `Module.Basis.coe_linearEquivMulEquivGL_apply`: the matrix entry formula
  `(b.linearEquivMulEquivGL e) i j = b.repr (e (b j)) i`, matching Mathlib's convention for
  `LinearMap.toMatrix` (column `j` records the image of the `j`-th basis vector).
* `Module.Basis.linearEquivMulEquivGL_symm`: the two chains agree,
  `b.linearEquivMulEquivGL.symm = (Matrix.GeneralLinearGroup.toLin' b).trans
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M)`.
-/

namespace Module.Basis

variable {R M n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype n] [DecidableEq n]

/-- **A basis identifies `Aut_R(M)` with `GL n R`.** The forward map sends an `R`-linear
automorphism to its matrix in the basis `b`; it is multiplicative because
`LinearMap.toMatrixAlgEquiv` is an algebra equivalence, and lands in the units because an
automorphism is invertible. -/
noncomputable def linearEquivMulEquivGL (b : Basis n R M) :
    (M ≃ₗ[R] M) ≃* Matrix.GeneralLinearGroup n R :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)

/-- **The matrix entries.** Column `j` of the matrix of `e` is the coordinate vector of `e (b j)`,
which is Mathlib's convention for `LinearMap.toMatrix`. -/
@[simp]
theorem coe_linearEquivMulEquivGL_apply (b : Basis n R M) (e : M ≃ₗ[R] M) (i j : n) :
    (b.linearEquivMulEquivGL e : Matrix n n R) i j = b.repr (e (b j)) i := by
  change LinearMap.toMatrixAlgEquiv b (e : M →ₗ[R] M) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

/-- The inverse of `b.linearEquivMulEquivGL e` is the matrix of `e.symm`. -/
theorem coe_inv_linearEquivMulEquivGL_apply (b : Basis n R M) (e : M ≃ₗ[R] M) (i j : n) :
    (((b.linearEquivMulEquivGL e)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R) i j
      = b.repr (e.symm (b j)) i := by
  have : (b.linearEquivMulEquivGL e)⁻¹ = b.linearEquivMulEquivGL e.symm := by
    rw [← map_inv]
    rfl
  rw [this, coe_linearEquivMulEquivGL_apply]

/-- **The two chains from a basis to `GL n R` agree.** `b.linearEquivMulEquivGL` goes `Aut → GL`
through `LinearMap.toMatrixAlgEquiv`; the Mathlib composite
`(Matrix.GeneralLinearGroup.toLin' b).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R M)`
goes `GL → Aut` through `Matrix.toLinAlgEquiv`. Both send a matrix `A` to the endomorphism
`v ↦ ∑ i, (A *ᵥ b.repr v) i • b i`, so they are mutually inverse — in particular the two
conventions differ by no transpose.

⚠️ Nothing here is about a prime, a Tate module or an elliptic curve; see the module docstring for
why this used to be stated only for a basis of `T₂E`. -/
theorem linearEquivMulEquivGL_symm (b : Basis n R M) :
    b.linearEquivMulEquivGL.symm
      = (Matrix.GeneralLinearGroup.toLin' b).trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv R M) := by
  refine MulEquiv.ext fun A => LinearEquiv.ext fun v => ?_
  have hl : ((Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R M)) A v
      = (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv v := rfl
  have hr : b.linearEquivMulEquivGL.symm A v
      = Matrix.toLinAlgEquiv b (A : Matrix n n R) v := rfl
  rw [hl, Matrix.GeneralLinearGroup.toLin'_apply b A v, Fintype.linearCombination_apply, hr,
    Matrix.toLinAlgEquiv_apply]

end Module.Basis
