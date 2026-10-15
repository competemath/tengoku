/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.Matrix.Conj

/-!

# Reshaping matrices

This defines the identification between `Mₙₓₘ(R)` and `Rⁿˣᵐ` (see `matrix.reshape`),
and shows some obvious properties of this identification.

-/

@[expose] public section

namespace Matrix

open scoped Matrix

variable {R I J : Type _} [Semiring R]

/-- identifies matrices $M_{I\times J}(R)$ with $R^{I \times J}$,
  this is given by $\varrho (x)_{(i,j)} = x_{ij}$ -/
def reshape : Matrix I J R ≃ₗ[R] I × J → R :=
  (LinearEquiv.curry R _ _ _).symm

/--
@isnad1 id=eq.0h5v.s8.c71ad74928b0 from=translated src=- shape=72d7a07a vocab=a09f0c03
-/
theorem reshape_apply (x : Matrix I J R) (ij : I × J) : reshape x ij = x ij.1 ij.2 :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.91ded3075918 from=translated src=- shape=f53df5ba vocab=c8a0554a
-/
theorem reshape_symm_apply (x : I × J → R) (i : I) (j : J) :
    (reshape : Matrix I J R ≃ₗ[R] I × J → R).symm x i j = x (i, j) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.fc7caca7231b from=translated src=- shape=5d025d93 vocab=56e303bb
-/
theorem reshape_symm_apply' (x : I × J → R) (ij : I × J) :
    (reshape : Matrix I J R ≃ₗ[R] I × J → R).symm x ij.1 ij.2 = x ij := by
  rw [reshape_symm_apply x ij.1 ij.2, Prod.mk.eta]

/--
@isnad1 id=eq.0h4v.s8.698fe0ad4f52 from=translated src=- shape=e53bdd28 vocab=b42defa5
-/
theorem reshape_one [DecidableEq I] (x y : I) :
    reshape (1 : Matrix I I R) (x, y) = ite (x = y) 1 0 := by
  simp_rw [Matrix.reshape_apply, Matrix.one_apply]

/-- ${\varrho(x)}^*=\varrho(\bar{x})$
@isnad1 id=eq.0h4v.s9.6b95bd620d1a from=translated src=- shape=ff5bdde8 vocab=d666998a
-/
theorem reshape_aux_star [Star R] (x : Matrix I J R) : star (reshape x) = reshape xᴴᵀ := by
  ext1
  simp_rw [Pi.star_apply, Matrix.reshape_apply, Matrix.conj_apply]

end Matrix
