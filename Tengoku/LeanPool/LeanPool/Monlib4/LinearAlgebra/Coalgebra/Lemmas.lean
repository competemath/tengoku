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

/--
@isnad1 id=eq.0h7v.s8.9209de15901e from=translated src=- shape=2e7b85b9 vocab=b2062741
-/
theorem TensorProduct.map_left_up {R A B C D : Type*}
  [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map f LinearMap.id) ∘ₗ (map LinearMap.id g) :=
ext rfl
/--
@isnad1 id=eq.0h7v.s8.9209de15901e from=translated src=- shape=2e7b85b9 vocab=b2062741
-/
alias TensorProduct.map_right_down := TensorProduct.map_left_up

/--
@isnad1 id=eq.0h7v.s8.2c7ff8e7d483 from=translated src=- shape=abfc42d8 vocab=b2062741
-/
theorem TensorProduct.map_right_up {R A B C D : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map LinearMap.id g) ∘ₗ (map f LinearMap.id) :=
ext rfl
/--
@isnad1 id=eq.0h7v.s8.2c7ff8e7d483 from=translated src=- shape=abfc42d8 vocab=b2062741
-/
alias TensorProduct.map_left_down := TensorProduct.map_right_up

open TensorProduct LinearMap
/--
@isnad1 id=eq.0h2v.s11.2f4e20d43c90 from=translated src=- shape=ed7cc221 vocab=55871744
-/
theorem Algebra.linearMap_mul'_assoc {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (map (mul' R A) LinearMap.id)
  = (mul' R A) ∘ₗ (map LinearMap.id (mul' R A))
    ∘ₗ (_root_.TensorProduct.assoc R A A A) := by
  refine TensorProduct.ext_threefold ?_
  intro x y z
  simp only [coe_comp, Function.comp_apply, map_tmul, mul'_apply, id_coe, id_eq,
    LinearEquiv.coe_coe, assoc_tmul, mul_assoc]
/--
@isnad1 id=eq.0h2v.s11.2f4e20d43c90 from=translated src=- shape=ed7cc221 vocab=55871744
-/
alias Algebra.assoc := Algebra.linearMap_mul'_assoc

/--
@isnad1 id=eq.0h2v.s11.afff557ab90d from=translated src=- shape=8b44ba0c vocab=5f698428
-/
theorem Algebra.assoc' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (mul' R A))
    = (mul' R A) ∘ₗ (lTensor A (mul' R A)) ∘ₗ (_root_.TensorProduct.assoc R A A A) :=
Algebra.assoc
/--
@isnad1 id=eq.0h2v.s11.afff557ab90d from=translated src=- shape=8b44ba0c vocab=5f698428
-/
alias Algebra.mul_comp_rTensor_mul := Algebra.assoc'

open scoped TensorProduct
/--
@isnad1 id=eq.0h2v.s9.5b83c3582484 from=translated src=- shape=74e0cb6c vocab=eb0e5c21
-/
theorem Algebra.mul_comp_rTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.lid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.rTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, lid_tmul, algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
/--
@isnad1 id=eq.0h2v.s9.b471fd9e0ad9 from=translated src=- shape=5b5c7fd0 vocab=536a38e0
-/
theorem Algebra.mul_comp_rTensor_unit_comp_lid_symm
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
    ∘ₗ (_root_.TensorProduct.lid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_rTensor_unit]
  simp

/--
@isnad1 id=eq.0h2v.s9.84cb6f465b02 from=translated src=- shape=d0b5bd38 vocab=22ce8633
-/
theorem Algebra.mul_comp_lTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.rid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.lTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.rid_tmul, algebraMap_eq_smul_one,
    mul_smul_comm, mul_one]

/--
@isnad1 id=eq.0h2v.s9.4bec81b60767 from=translated src=- shape=3fdf08b5 vocab=e0cf965d
-/
theorem Algebra.mul_comp_lTensor_unit_comp_rid_symm
  {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A)) ∘ₗ (_root_.TensorProduct.rid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_lTensor_unit]
  simp

open Coalgebra
/--
@isnad1 id=eq.0h2v.s9.674611b3586c from=translated src=- shape=9a541ae6 vocab=8c9b4df1
-/
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

/--
@isnad1 id=eq.0h2v.s9.59f12171abab from=translated src=- shape=e8479b29 vocab=92bf3b0e
-/
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

/--
@isnad1 id=eq.0h2v.s9.746c3fa69e0e from=translated src=- shape=2e852f36 vocab=eeab8384
-/
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

/--
@isnad1 id=eq.0h2v.s9.1dbdb248c033 from=translated src=- shape=8863c92d vocab=4bd892f8
-/
lemma Coalgebra.rTensor_counit_comp_comul'
  {A : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A] :
  ((rT _ counit) ∘ₗ comul) = (TensorProduct.lid R A).symm.toLinearMap := by
  rw [rTensor_counit_comp_comul]
  rfl

/--
@isnad1 id=eq.0h6v.s10.5515fb210944 from=translated src=- shape=2359b8d6 vocab=d1394f2f
-/
lemma TensorProduct.assoc_symm_comp_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (LinearEquiv.symm (ϰ D B C)) ∘ₗ (rT _ x) =
    (rT _ (rT _ x))
      ∘ₗ (LinearEquiv.symm (ϰ A B C)).toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp_all
/--
@isnad1 id=eq.0h6v.s10.edf94bd925fb from=translated src=- shape=9d0036f3 vocab=3f266e6f
-/
lemma TensorProduct.assoc_symm_comp_lTensor_lTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (ϰ B C D).symm.toLinearMap ∘ₗ (lT _ (lT _ x)) =
    (lT _ x) ∘ₗ (ϰ B C A).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp_all

/--
@isnad1 id=eq.0h6v.s10.7494ce206798 from=translated src=- shape=1efe72a0 vocab=64726524
-/
lemma TensorProduct.rTensor_lTensor_comp_assoc_symm {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (rT _ (lT _ x)) ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap =
    (LinearEquiv.symm (ϰ B D C)).toLinearMap ∘ₗ (lT _ (rT _ x)) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]
/--
@isnad1 id=eq.0h6v.s10.e217755c5198 from=translated src=- shape=271e5ed0 vocab=0ce9e8ab
-/
lemma TensorProduct.assoc_comp_rTensor_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  (ϰ D B C).toLinearMap ∘ₗ (rT _ (rT _ x)) = (rT _ x) ∘ₗ (ϰ _ _ _).toLinearMap := by
  apply TensorProduct.ext_threefold
  simp_all

/--
@isnad1 id=eq.1h8v.s11.1a74b90b65d6 from=translated src=- shape=e6df4bbf vocab=c676f709
-/
lemma TensorProduct.ext_fourfold_right {A B C D E : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [AddCommMonoid E]
  [Module R A] [Module R B] [Module R C] [Module R D]
  [Module R E] {f g : (A ⊗[R] (B ⊗[R] (C ⊗[R] D))) →ₗ[R] E} :
  (∀ x y z w, f (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w))) = g (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w)))) → f = g := by
  intro h
  ext x y z w
  exact h x y z w

/--
@isnad1 id=eq.0h5v.s12.09d7037c28a0 from=translated src=- shape=81ce233e vocab=64726524
-/
lemma TensorProduct.assoc_comp_rTensor_assoc_symm_comp_assoc_symm_comp_lTensor_assoc_symm
  {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (ϰ _ _ _).toLinearMap ∘ₗ (rT _ (ϰ _ _ _).symm.toLinearMap) ∘ₗ (ϰ _ _ _).symm.toLinearMap
    ∘ₗ (lT _ (ϰ _ _ _).symm.toLinearMap) = (ϰ A B (C ⊗[R] D)).symm.toLinearMap := by
  apply TensorProduct.ext_fourfold_right
  simp_all

/--
@isnad1 id=eq.0h7v.s8.191820d85e3c from=translated src=- shape=47e648a9 vocab=5b500433
-/
lemma TensorProduct.rTensor_comp_rTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
  (rT D x) ∘ₗ (rT D y) = rT D (x ∘ₗ y) := by
  simp_rw [rTensor, ← map_comp, id_comp]
/--
@isnad1 id=eq.0h7v.s8.8947cd20b864 from=translated src=- shape=96cb8142 vocab=409b469a
-/
lemma TensorProduct.lTensor_comp_lTensor {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
  (lT D x) ∘ₗ (lT D y) = lT D (x ∘ₗ y) := by
  simp_rw [lTensor, ← map_comp, id_comp]

/--
@isnad1 id=eq.0h3v.s10.4f0b46e4a3fd from=translated src=- shape=9381ecfa vocab=0e244b69
-/
lemma lid_tensor_toLinearMap {A B : Type*} [AddCommMonoid A]
  [Module R A] [AddCommMonoid B] [Module R B] :
  (τ (A ⊗[R] B)).toLinearMap
    = rT _ (τ _).toLinearMap ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap := by
  simpa [LinearEquiv.coe_trans] using
    congrArg LinearEquiv.toLinearMap (TensorProduct.lid_tensor (R := R) (M := A) (N := B))

/--
@isnad1 id=eq.0h3v.s10.4f0b46e4a3fd from=translated src=- shape=9381ecfa vocab=0e244b69
-/
lemma lid_tensor {A B : Type*} [AddCommMonoid A]
  [Module R A] [AddCommMonoid B] [Module R B] :
  (τ (A ⊗[R] B)).toLinearMap
    = rT _ (τ _).toLinearMap ∘ₗ (LinearEquiv.symm (ϰ _ _ _)).toLinearMap :=
lid_tensor_toLinearMap

/--
@isnad1 id=eq.0h7v.s8.1b3f26949eab from=translated src=- shape=bfb22784 vocab=269bbb9e
-/
lemma rTensor_comp_lTensor' {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] B) (y : C →ₗ[R] D) :
  (rT _ x) ∘ₗ (lT _ y) = (lT _ y) ∘ₗ (rT _ x) := by
  simp only [rTensor_comp_lTensor, lTensor_comp_rTensor]

variable {A : Type*} [Semiring A] [Algebra R A]
  [Coalgebra R A]

open TensorProduct

/--
@isnad1 id=eq.0h2v.s9.d8a84abff9a9 from=translated src=- shape=b73a4b66 vocab=9fb98a99
-/
theorem counit_comp_mul_comp_rTensor_unit_eq_counit :
  counit ∘ₗ (m A) ∘ₗ (rT _ (Algebra.linearMap R A)) = counit ∘ₗ (τ _).toLinearMap := by
  rw [Algebra.mul_comp_rTensor_unit]
/--
@isnad1 id=eq.0h2v.s9.c15427de4fea from=translated src=- shape=f53ea1ad vocab=6b46141b
-/
theorem counit_comp_mul_comp_lTensor_unit_eq_counit :
  counit ∘ₗ (m A) ∘ₗ (lT _ (Algebra.linearMap R A))
    = counit ∘ₗ (TensorProduct.rid _ _).toLinearMap := by
  rw [Algebra.mul_comp_lTensor_unit]
/--
@isnad1 id=eq.0h2v.s9.ec72acd6aad1 from=translated src=- shape=b822a348 vocab=8426623b
-/
theorem rTensor_counit_comp_comul_comp_unit_eq_unit :
  (rT _ counit) ∘ₗ comul ∘ₗ Algebra.linearMap R A
    = (τ _).symm.toLinearMap ∘ₗ Algebra.linearMap R A := by
  rw [← LinearMap.comp_assoc, rTensor_counit_comp_comul]
  rfl
/--
@isnad1 id=eq.0h2v.s9.08b4a5a37c00 from=translated src=- shape=ac6e78b8 vocab=eeab8384
-/
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
