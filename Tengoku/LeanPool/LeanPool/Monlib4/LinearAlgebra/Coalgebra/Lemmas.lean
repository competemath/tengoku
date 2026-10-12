/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas`.
-/

@[expose] public section

theorem TensorProduct.map_left_up {R A B C D : Type*}
  [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map f LinearMap.id) ∘ₗ (map LinearMap.id g) :=
ext rfl
alias TensorProduct.map_right_down := TensorProduct.map_left_up

theorem TensorProduct.map_right_up {R A B C D : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map LinearMap.id g) ∘ₗ (map f LinearMap.id) :=
ext rfl
alias TensorProduct.map_left_down := TensorProduct.map_right_up

open TensorProduct LinearMap
theorem Algebra.linearMap_mul'_assoc {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (map (mul' R A) LinearMap.id)
  = (mul' R A) ∘ₗ (map LinearMap.id (mul' R A))
    ∘ₗ (_root_.TensorProduct.assoc R A A A) := by
  refine TensorProduct.ext_threefold ?_
  intro x y z
  simp only [coe_comp, Function.comp_apply, map_tmul, mul'_apply, id_coe, id_eq,
    LinearEquiv.coe_coe, assoc_tmul, mul_assoc]
alias Algebra.assoc := Algebra.linearMap_mul'_assoc

theorem Algebra.assoc' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (mul' R A))
    = (mul' R A) ∘ₗ (lTensor A (mul' R A)) ∘ₗ (_root_.TensorProduct.assoc R A A A) :=
Algebra.assoc
alias Algebra.mul_comp_rTensor_mul := Algebra.assoc'

open scoped TensorProduct
theorem Algebra.mul_comp_rTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.lid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.rTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, lid_tmul, algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
theorem Algebra.mul_comp_rTensor_unit_comp_lid_symm
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
    ∘ₗ (_root_.TensorProduct.lid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_rTensor_unit]
  simp

theorem Algebra.mul_comp_lTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.rid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.lTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.rid_tmul, algebraMap_eq_smul_one,
    mul_smul_comm, mul_one]

theorem Algebra.mul_comp_lTensor_unit_comp_rid_symm
  {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A)) ∘ₗ (_root_.TensorProduct.rid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_lTensor_unit]
  simp

open Coalgebra
theorem counit_comp_mul_comp_rTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  counit ∘ₗ (LinearMap.mul' R _) ∘ₗ
    (LinearMap.rTensor A (Algebra.linearMap R A))
    ∘ₗ (TensorProduct.lid R A).symm.toLinearMap
  = counit :=
calc counit ∘ₗ (LinearMap.mul' R _) ∘ₗ
  (LinearMap.rTensor A (Algebra.linearMap R A))
      ∘ₗ ((TensorProduct.mk R _ _) 1)
    = counit ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ ((TensorProduct.mk R R A) 1) :=
      by simp_rw [← Algebra.mul_comp_rTensor_unit, LinearMap.comp_assoc]
  _ = counit := by aesop

theorem counit_comp_mul_lTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  counit ∘ₗ (mul' R _) ∘ₗ
    (lTensor A (Algebra.linearMap R A))
    ∘ₗ (TensorProduct.rid R A).symm.toLinearMap
  = counit :=
calc counit ∘ₗ (mul' R _) ∘ₗ (lTensor A (Algebra.linearMap R A))
      ∘ₗ ((TensorProduct.mk R A R).flip 1)
    = counit ∘ₗ (TensorProduct.rid R A).toLinearMap ∘ₗ ((TensorProduct.mk R A R).flip 1) :=
      by simp_rw [← Algebra.mul_comp_lTensor_unit, LinearMap.comp_assoc]
  _ = counit := by aesop

theorem lTensor_counit_comp_comul_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  (lTensor A counit) ∘ₗ comul ∘ₗ (Algebra.linearMap R A)
  = (TensorProduct.rid R A).symm ∘ₗ (Algebra.linearMap R A) := by
  ext
  simp_all only [LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, _root_.map_one, lTensor_counit_comul,
    LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]

variable {R : Type*} [CommSemiring R]

local notation "lT" => LinearMap.lTensor
local notation "rT" => LinearMap.rTensor
local notation "m" => LinearMap.mul' R
local notation "ϰ" => TensorProduct.assoc R
local notation "τ" => TensorProduct.lid R
local notation x " ⊗ₘ " y => TensorProduct.map x y
-- local notation "ϰ⁻¹" => LinearEquiv.symm ϰ

lemma Coalgebra.rTensor_counit_comp_comul'
  {A : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A] :
  ((rT _ counit) ∘ₗ comul) = (TensorProduct.lid R A).symm.toLinearMap := by
  rw [rTensor_counit_comp_comul]
  rfl

lemma TensorProduct.assoc_symm_comp_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (LinearEquiv.symm (ϰ D B C)) ∘ₗ (rT _ x) =
    (rT _ (rT _ x))
      ∘ₗ (LinearEquiv.symm (ϰ A B C)).toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp_all
lemma TensorProduct.assoc_symm_comp_lTensor_lTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (ϰ B C D).symm.toLinearMap ∘ₗ (lT _ (lT _ x)) =
    (lT _ x) ∘ₗ (ϰ B C A).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp_all

lemma TensorProduct.rTensor_lTensor_comp_assoc_symm {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (rT _ (lT _ x)) ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap =
    (LinearEquiv.symm (ϰ B D C)).toLinearMap ∘ₗ (lT _ (rT _ x)) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]
lemma TensorProduct.assoc_comp_rTensor_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (ϰ D B C).toLinearMap ∘ₗ (rT _ (rT _ x)) = (rT _ x) ∘ₗ (ϰ _ _ _).toLinearMap := by
  apply TensorProduct.ext_threefold
  simp_all

lemma TensorProduct.ext_fourfold_right {A B C D E : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [AddCommMonoid E]
  [Module R A] [Module R B] [Module R C] [Module R D]
  [Module R E] {f g : (A ⊗[R] (B ⊗[R] (C ⊗[R] D))) →ₗ[R] E} :
  (∀ x y z w, f (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w))) = g (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w)))) → f = g := by
  intro h
  ext x y z w
  exact h x y z w

lemma TensorProduct.assoc_comp_rTensor_assoc_symm_comp_assoc_symm_comp_lTensor_assoc_symm
  {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (ϰ _ _ _).toLinearMap ∘ₗ (rT _ (ϰ _ _ _).symm.toLinearMap) ∘ₗ (ϰ _ _ _).symm.toLinearMap
    ∘ₗ (lT _ (ϰ _ _ _).symm.toLinearMap) = (ϰ A B (C ⊗[R] D)).symm.toLinearMap := by
  apply TensorProduct.ext_fourfold_right
  simp_all

lemma TensorProduct.rTensor_comp_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
  (rT D x) ∘ₗ (rT D y) = rT D (x ∘ₗ y) := by
  simp_rw [rTensor, ← map_comp, id_comp]
lemma TensorProduct.lTensor_comp_lTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
  (lT D x) ∘ₗ (lT D y) = lT D (x ∘ₗ y) := by
  simp_rw [lTensor, ← map_comp, id_comp]

lemma lid_tensor_toLinearMap {A B : Type*} [AddCommMonoid A]
  [Module R A] [AddCommMonoid B] [Module R B] :
  (τ (A ⊗[R] B)).toLinearMap
    = rT _ (τ _).toLinearMap ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap := by
  simpa [LinearEquiv.coe_trans] using
    congrArg LinearEquiv.toLinearMap (TensorProduct.lid_tensor (R := R) (M := A) (N := B))

lemma lid_tensor {A B : Type*} [AddCommMonoid A]
  [Module R A] [AddCommMonoid B] [Module R B] :
  (τ (A ⊗[R] B)).toLinearMap
    = rT _ (τ _).toLinearMap ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap :=
lid_tensor_toLinearMap

lemma rTensor_comp_lTensor' {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] B) (y : C →ₗ[R] D) :
  (rT _ x) ∘ₗ (lT _ y) = (lT _ y) ∘ₗ (rT _ x) := by
  simp only [rTensor_comp_lTensor, lTensor_comp_rTensor]

variable {A : Type*} [Semiring A] [Algebra R A]
  [Coalgebra R A]

open TensorProduct

theorem counit_comp_mul_comp_rTensor_unit_eq_counit :
  counit ∘ₗ (m A) ∘ₗ (rT _ (Algebra.linearMap R A)) = counit ∘ₗ (τ _).toLinearMap := by
  rw [Algebra.mul_comp_rTensor_unit]
theorem counit_comp_mul_comp_lTensor_unit_eq_counit :
  counit ∘ₗ (m A) ∘ₗ (lT _ (Algebra.linearMap R A))
    = counit ∘ₗ (TensorProduct.rid _ _).toLinearMap := by
  rw [Algebra.mul_comp_lTensor_unit]
theorem rTensor_counit_comp_comul_comp_unit_eq_unit :
  (rT _ counit) ∘ₗ comul ∘ₗ Algebra.linearMap R A
    = (τ _).symm.toLinearMap ∘ₗ Algebra.linearMap R A := by
  rw [← LinearMap.comp_assoc, rTensor_counit_comp_comul]
  rfl
theorem lTensor_counit_comp_comul_comp_unit_eq_unit :
  (lT _ counit) ∘ₗ comul ∘ₗ Algebra.linearMap R A
    = (TensorProduct.rid _ _).symm.toLinearMap ∘ₗ Algebra.linearMap R A := by
  rw [← LinearMap.comp_assoc, lTensor_counit_comp_comul]
  rfl

/-- An algebra and coalgebra with the Frobenius tensor compatibility law. -/
class FrobeniusAlgebra (R A : Type*) [CommSemiring R] [Semiring A] extends
  Algebra R A, Coalgebra R A where
    lTensor_mul_comp_rTensor_comul_commute :
      (lT A (LinearMap.mul' R A))
        ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
        ∘ₗ (rT A comul)
      = (rT A (LinearMap.mul' R A))
        ∘ₗ (TensorProduct.assoc _ _ _ _).symm.toLinearMap
        ∘ₗ (lT A comul)

attribute [instance] FrobeniusAlgebra.toAlgebra
attribute [instance] FrobeniusAlgebra.toCoalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [FrobeniusAlgebra R A]
