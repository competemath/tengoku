/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# LeanPool.Monlib4.LinearAlgebra.LinearMapOp

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.LinearMapOp`.
-/

@[expose] public section

/-- Push a semilinear map between modules through the multiplicative opposite. -/
@[simps]
def LinearMap.op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ where
    toFun x := MulOpposite.op (f (MulOpposite.unop x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]

/-- Pull a semilinear map between opposite modules back through the multiplicative opposite. -/
@[simps]
def LinearMap.unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) : M →ₛₗ[σ] M₂ where
    toFun x := MulOpposite.unop (f (MulOpposite.op x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]
/--
@isnad1 id=eq.0h6v.s6.0d4512775913 from=translated src=- shape=e3b02580 vocab=274b2dea
-/
@[simp]
lemma LinearMap.unop_op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) :
  f.unop.op = f :=
rfl
/--
@isnad1 id=eq.0h6v.s6.787eb5aa24aa from=translated src=- shape=b0738351 vocab=6caf4799
-/
@[simp]
lemma LinearMap.op_unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) :
  f.op.unop = f :=
rfl

/--
@isnad1 id=eq.0h4v.s8.597e97be7dfb from=translated src=- shape=7dc8bdc8 vocab=5623c7eb
-/
@[simp]
theorem AlgEquiv.op_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] (f : A ≃ₐ[R] B) :
  f.op.toLinearMap = f.toLinearMap.op :=
rfl
