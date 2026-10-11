/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.ExtendScalar

Imported Lean Pool material for `LeanPool.BrauerGroupNew.ExtendScalar`.
-/

@[expose] public section

open scoped TensorProduct

universe u
variable (k K L A : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
  [Algebra k L] [Ring A] [Algebra k A] [IsScalarTower k K L]

/-- Additive map sending `l ⊗ a` to `l ⊗ (1 ⊗ a)` after releasing scalars through `K`. -/
def releaseAddHom : L ⊗[k] A →+ L ⊗[K] (K ⊗[k] A) :=
  TensorProduct.liftAddHom
  {
    toFun l := {
      toFun a := l ⊗ₜ[K] (1 ⊗ₜ[k] a)
      map_zero' := by simp only [TensorProduct.tmul_zero]
      map_add' _ _ := by simp_rw [TensorProduct.tmul_add]
    }
    map_zero' := by simp only [TensorProduct.zero_tmul]; rfl
    map_add' x y := by
      ext a'
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
      repeat rw [TensorProduct.add_tmul]
  } fun r l a ↦ by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.tmul_smul]; rfl

/-- Linear map sending `m ⊗ a` to `(m • l) ⊗ a`. -/
def absorbMap (l : L) : K ⊗[k] A →ₗ[k] L ⊗[k] A :=
  TensorProduct.lift {
    toFun := fun m ↦ {
      toFun := fun a ↦ (m • l) ⊗ₜ[k] a
      map_add' := fun _ _ ↦ by simp only [TensorProduct.tmul_add]
      map_smul' := fun _ _ ↦ by simp [TensorProduct.tmul_smul, RingHom.id_apply]
    }
    map_add' := fun _ _ ↦ by ext; simp only [add_smul, TensorProduct.add_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := fun _ _ ↦ by ext; simp only [smul_assoc, ← TensorProduct.smul_tmul',
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
  }
