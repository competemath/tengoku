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

/--
@isnad1 id=eq.0h12v.s9.a4fb21b044c5 from=translated src=- shape=a1aa22cf vocab=b2d5ce1d
-/
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

/--
@isnad1 id=eq.0h6v.s9.ef1b92bd2992 from=translated src=- shape=1a2c639d vocab=e5c13bdf
-/
lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
/--
@isnad1 id=eq.0h2v.s8.821ea9363e68 from=translated src=- shape=93bfb723 vocab=9fa62f75
-/
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

/--
@isnad1 id=eq.0h7v.s8.bdaee2e20a2c from=translated src=- shape=bc3c1a08 vocab=43670c9e
-/
lemma AlgEquiv.lTensor_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : A) :
  (AlgEquiv.lTensor C f) (x ⊗ₜ[R] y) = x ⊗ₜ f (y) :=
rfl
/--
@isnad1 id=eq.0h7v.s8.f2c809e26ae9 from=translated src=- shape=9bbe0dcf vocab=a07aac02
-/
lemma AlgEquiv.lTensor_symm_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : B) :
  (AlgEquiv.lTensor C f).symm (x ⊗ₜ[R] y) = x ⊗ₜ f.symm (y) :=
rfl
