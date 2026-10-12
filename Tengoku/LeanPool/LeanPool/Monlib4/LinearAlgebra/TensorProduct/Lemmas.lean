/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# Tensor-product map lemmas

This file contains compatibility lemmas and equivalences for tensor-product
maps used by the Monlib4 port.
-/

@[expose] public section

open scoped TensorProduct

theorem TensorProduct.map_apply_map_apply {R : Type _} [CommSemiring R] {A B C D E F : Type _}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [AddCommMonoid E]
    [AddCommMonoid F] [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (z : B →ₗ[R] E) (w : D →ₗ[R] F) (x : A ⊗[R] C) :
    (TensorProduct.map z w) (TensorProduct.map f g x) = TensorProduct.map (z.comp f) (w.comp g) x :=
  by
  revert x
  simp_rw [← LinearMap.comp_apply, ← LinearMap.ext_iff]
  apply TensorProduct.ext'
  simp_all

local notation
  f " ⊗ₘ " g => _root_.TensorProduct.map f g

lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
@[simp]
lemma AlgEquiv.op_one {R A : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] :
  AlgEquiv.op (1 : A ≃ₐ[R] A) = 1 :=
rfl

/-- Tensor an algebra equivalence on the left by a fixed algebra. -/
noncomputable def AlgEquiv.lTensor {R A B : Type*} (C : Type*) [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) :
  (C ⊗[R] A) ≃ₐ[R] (C ⊗[R] B) :=
Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
  (LinearEquiv.lTensor C f.toLinearEquiv)
  (by
    simp only [toLinearEquiv_apply, LinearEquiv.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.map_mul, implies_true])
  (by simp only [toLinearEquiv_apply, map_one, LinearEquiv.lTensor_tmul]; rfl)

lemma AlgEquiv.lTensor_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : A) :
  (AlgEquiv.lTensor C f) (x ⊗ₜ[R] y) = x ⊗ₜ f (y) :=
rfl
lemma AlgEquiv.lTensor_symm_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : B) :
  (AlgEquiv.lTensor C f).symm (x ⊗ₜ[R] y) = x ⊗ₜ f.symm (y) :=
rfl
