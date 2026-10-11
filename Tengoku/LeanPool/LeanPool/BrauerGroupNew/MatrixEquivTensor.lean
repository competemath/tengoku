/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.MatrixEquivTensor

Imported Lean Pool material for `LeanPool.BrauerGroupNew.MatrixEquivTensor`.
-/

@[expose] public section

open scoped TensorProduct

variable (K F : Type*) [CommSemiring K] [CommSemiring F] [Algebra F K]
    (A : Type*) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]

open Matrix

/-- Bilinear map sending a scalar and a matrix to the matrix obtained by tensoring entries. -/
def toTensorMartrixToFunBilinear : K →ₗ[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) where
  toFun k := {
    toFun M := k • Algebra.TensorProduct.includeRight.mapMatrix M
    map_add' _ _ := by simp [← smul_add, map_add]
    map_smul' r M := by simpa using smul_comm _ _ _
  }
  map_add' k1 k2 := by ext; simp [add_smul]
  map_smul' r k := by ext; simp

@[simp]
lemma toTensorMartrixToFunBilinear_apply (k : K) (M : Matrix n n A) :
  toTensorMartrixToFunBilinear K F A n k M =
  k • Algebra.TensorProduct.includeRight.mapMatrix M := rfl

/-- The `F`-linear map induced from `toTensorMartrixToFunBilinear`. -/
abbrev toTensorMatrixToFunFlinear : K ⊗[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) :=
  TensorProduct.lift <| toTensorMartrixToFunBilinear K F A n

open TensorProduct

/-- Bilinear map placing a tensor entry into the `(i,j)` matrix coefficient. -/
def invFunToFunBilinear (i j : n) : K →ₗ[F] A →ₗ[F] K ⊗[F] Matrix n n A where
  toFun k := {
    toFun a := k ⊗ₜ single i j a
    map_add' _ _ := by simp [single_add, tmul_add]
    map_smul' _ _ := by simp [← smul_single]
  }
  map_add' _ _ := by ext; simp [add_tmul]
  map_smul' _ _ := by ext; simp [smul_tmul']

omit [Fintype n] in
@[simp]
lemma invFunToFunBilinear_apply (i j : n) (k : K) (a : A) :
  invFunToFunBilinear K F A n i j k a = k ⊗ₜ single i j a := rfl

/-- The `F`-linear map induced by `invFunToFunBilinear`. -/
abbrev invFunToFun (i j : n) : K ⊗[F] A →ₗ[F] K ⊗[F] Matrix n n A :=
  TensorProduct.lift <| invFunToFunBilinear K F A n i j
