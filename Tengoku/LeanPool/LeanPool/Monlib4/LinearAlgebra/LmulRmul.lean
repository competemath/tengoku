/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.LinearMapOp

/-!
# lmul and rmul

The left and right multiplication maps, copied from `LinearMap.mulLeft` and
`LinearMap.mulRight` but defined as linear maps.

-/

@[expose] public section

section

variable {R E F : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocSemiring F] [Module R E] [Module R F] [SMulCommClass R E E]
  [SMulCommClass R F F] [IsScalarTower R E E] [IsScalarTower R F F]

omit [IsScalarTower R E E] [IsScalarTower R F F] in
/--
@isnad1 id=eq.0h7v.s8.c1729f43fba1 from=translated src=- shape=f10cc7f0 vocab=59578bd6
-/
theorem LinearMap.mulLeft_conj_of_mulEquivClass_apply
  {Fn : Type*} [EquivLike Fn E F] [MulEquivClass Fn E F]
  (f : Fn) (x : E) (y : F) :
    f (LinearMap.mulLeft R x (EquivLike.inv f y))  = LinearMap.mulLeft R (f x) y := by
  simp_all

omit [SMulCommClass R E E] [SMulCommClass R F F] in
/--
@isnad1 id=eq.0h7v.s8.7a471f73292b from=translated src=- shape=f10cc7f0 vocab=3e7486ab
-/
theorem LinearMap.mulRight_conj_of_mulEquivClass_apply
  {Fn : Type*} [EquivLike Fn E F] [MulEquivClass Fn E F]
  (f : Fn) (x : E) (y : F) :
    f (LinearMap.mulRight R x (EquivLike.inv f y)) = LinearMap.mulRight R (f x) y := by
  simp_all

end

local notation "l(" x "," y ")" => y →ₗ[x] y

variable {R H₁ H₂ : Type _} [CommSemiring R]
  -- [semiring H₁] [semiring H₂]
  -- [algebra R H₁] [algebra R H₂]
  [NonUnitalNonAssocSemiring H₁]
  [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] [NonUnitalNonAssocSemiring H₂]
  [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂]

/--
@isnad1 id=iff.0h3v.s8.642a0b7aa6a8 from=translated src=- shape=9569d755 vocab=7c8425c6
-/
theorem left_module_map_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] {x : l(R,H₁)} :
    (∀ a b : H₁, x (a * b) = a * x b) ↔ x = LinearMap.mulRight R (x 1) := by
  simp_rw [LinearMap.ext_iff, LinearMap.mulRight_apply]
  constructor <;> intro h <;> intros
  · rw [← h, mul_one]
  · rw [h, mul_assoc, ← h]

/--
@isnad1 id=iff.0h3v.s8.0f66788908e5 from=translated src=- shape=5fedf906 vocab=86829ec2
-/
theorem right_module_map_iff {H₂ : Type _} [Semiring H₂] [Algebra R H₂] {x : l(R,H₂)} :
    (∀ a b : H₂, x (a * b) = x a * b) ↔ x = LinearMap.mulLeft R (x 1) := by
  simp_rw [LinearMap.ext_iff, LinearMap.mulLeft_apply]
  constructor <;> intro h <;> intros
  · rw [← h, one_mul]
  · rw [h, ← mul_assoc, ← h]

/-- The linear map sending an element to left multiplication by that element. -/
def lmul : H₁ →ₗ[R] l(R,H₁) where
  toFun x := LinearMap.mulLeft R x
  map_add' x y := by
    ext1
    simp only [LinearMap.mulLeft_apply, add_mul, LinearMap.add_apply]
  map_smul' r x := by
    ext1
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, RingHom.id_apply, smul_mul_assoc]

/--
@isnad1 id=eq.0h4v.s8.5f90022118b5 from=translated src=- shape=d5ef5168 vocab=6f6c4217
-/
theorem lmul_apply (x y : H₁) : (lmul x : l(R,H₁)) y = x * y :=
  rfl

/--
@isnad1 id=eq.0h3v.s8.c62e28bde387 from=translated src=- shape=19ea232e vocab=d8792df0
-/
theorem lmul_eq_mul (x : H₁) : lmul x = LinearMap.mulLeft R x :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.58fed6ca22b1 from=translated src=- shape=8378dbe6 vocab=1869c922
-/
theorem lmul_eq_alg_lmul {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : l(R,H₁)) = Algebra.lmul R H₁ x :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.5ef6b8c95f99 from=translated src=- shape=6296cca8 vocab=f6cee473
-/
theorem lmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (lmul (1 : H₁) : l(R,H₁)) = 1 := by
    ext
    simp_rw [lmul_apply, Module.End.one_apply, one_mul]

/-- The linear map sending an element to right multiplication by that element. -/
def rmul : H₂ →ₗ[R] l(R,H₂) where
  toFun x := LinearMap.mulRight R x
  map_add' x y := by
    ext1
    simp only [LinearMap.mulRight_apply, mul_add, LinearMap.add_apply]
  map_smul' r x := by
    ext1
    simp only [LinearMap.mulRight_apply, LinearMap.smul_apply, RingHom.id_apply, mul_smul_comm]

/--
@isnad1 id=eq.0h4v.s8.d92828164f46 from=translated src=- shape=01f7ef74 vocab=21a7674e
-/
theorem rmul_apply (x y : H₂) : (rmul x : l(R,H₂)) y = y * x :=
  rfl

/--
@isnad1 id=eq.0h3v.s8.544ab0176650 from=translated src=- shape=19ea232e vocab=7c5b6e9c
-/
theorem rmul_eq_mul (x : H₂) : rmul x = LinearMap.mulRight R x :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.f37a7512b12c from=translated src=- shape=6296cca8 vocab=48e7caa2
-/
theorem rmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (rmul (1 : H₁) : l(R,H₁)) = 1 := by
  ext
  simp only [rmul_apply, mul_one, Module.End.one_apply]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

/-- Tensor right multiplication on the left factor with left multiplication on the right factor. -/
noncomputable def rmulMapLmul {R H₁ H₂ : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁]
  [NonUnitalNonAssocSemiring H₂] [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] :
  H₁ ⊗[R] H₂ →ₗ[R] ((H₁ ⊗[R] H₂) →ₗ[R] (H₁ ⊗[R] H₂)) :=
(TensorProduct.homTensorHomMap (.id R) H₁ H₂ H₁ H₂) ∘ₗ (TensorProduct.map rmul lmul)

/--
@isnad1 id=eq.0h5v.s10.3af603e16fed from=translated src=- shape=7753c8c4 vocab=a03081ab
-/
theorem rmulMapLmul_apply (x : H₁) (y : H₂) : rmulMapLmul (x ⊗ₜ[R] y) = rmul x ⊗ₘ lmul y := by
  rw [rmulMapLmul, LinearMap.comp_apply, TensorProduct.map_tmul,
    TensorProduct.homTensorHomMap_apply]

/--
@isnad1 id=eq.0h3v.s10.7964ea1e5b36 from=translated src=- shape=6d225785 vocab=deccaa46
-/
theorem rmulMapLmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] {H₂ : Type _} [NonAssocSemiring H₂] [Module R H₂]
    [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] : rmulMapLmul (1 ⊗ₜ 1 : H₁ ⊗[R] H₂) = 1 := by
  apply TensorProduct.ext'
  intro a b
  simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply, mul_one, one_mul,
    Module.End.one_apply]

open scoped BigOperators

/--
@isnad1 id=eq.0h5v.s8.864126690975 from=translated src=- shape=778d530b vocab=e184c846
-/
theorem LinearMap.mulLeft_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i ∈ s, LinearMap.mulLeft R (x i) = LinearMap.mulLeft R (∑ i ∈ s, x i) :=
by simp_rw [← lmul_eq_mul, map_sum]

/--
@isnad1 id=eq.0h5v.s8.676214dd64b5 from=translated src=- shape=778d530b vocab=02544e93
-/
theorem LinearMap.mulRight_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i ∈ s, LinearMap.mulRight R (x i) = LinearMap.mulRight R (∑ i ∈ s, x i) :=
by simp_rw [← rmul_eq_mul, map_sum]

/--
@isnad1 id=iff.0h3v.s9.a3b6a79bf777 from=translated src=- shape=7051a291 vocab=f3bc56a4
-/
theorem lmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : l(R,H₁)) = 0 ↔ x = 0 :=
  LinearMap.mulLeft_eq_zero_iff _ _ _

/--
@isnad1 id=iff.0h3v.s9.04b87c063937 from=translated src=- shape=7051a291 vocab=5b33aafd
-/
theorem rmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (rmul x : l(R,H₁)) = 0 ↔ x = 0 :=
  LinearMap.mulRight_eq_zero_iff _ _ _

/--
@isnad1 id=iff.0h3v.s9.8e569b4c6b2a from=translated src=- shape=729cfabc vocab=f6cee473
-/
theorem lmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (lmul x : l(R,H₁)) = 1 ↔ x = 1 := by
  simp_rw [LinearMap.ext_iff, lmul_apply, Module.End.one_apply]
  refine ⟨fun h => ?_, fun h a => by rw [h, one_mul]⟩
  simpa using h 1

/--
@isnad1 id=iff.0h3v.s8.21f54d3e807b from=translated src=- shape=22603206 vocab=5ef745a2
-/
theorem LinearMap.mulLeft_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulLeft R x = 1 ↔ x = 1 :=
  lmul_eq_one_iff _

/--
@isnad1 id=iff.0h3v.s9.1631d76486eb from=translated src=- shape=729cfabc vocab=48e7caa2
-/
theorem rmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (rmul x : l(R,H₁)) = 1 ↔ x = 1 := by
  simp_rw [LinearMap.ext_iff, rmul_apply, Module.End.one_apply]
  refine ⟨fun h => ?_, fun h a => by rw [h, mul_one]⟩
  simpa using h 1

/--
@isnad1 id=iff.0h3v.s8.eff7c9870956 from=translated src=- shape=22603206 vocab=6e778e5d
-/
theorem LinearMap.mulRight_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulRight R x = 1 ↔ x = 1 :=
  rmul_eq_one_iff _

/--
@isnad1 id=tfae.0h4v.s9.5115ff5597d6 from=translated src=- shape=38871554 vocab=c055f8c1
-/
theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae {H₁ : Type _} [Semiring H₁]
    [Algebra R H₁] (x : H₁) (p : Prop) [Decidable p] :
    List.TFAE [LinearMap.mulLeft R x = ite p 1 0,
      LinearMap.mulRight R x = ite p 1 0, x = ite p 1 0] := by
  by_cases h : p
  · simp_rw [h, ite_true, LinearMap.mulLeft_eq_one_iff, LinearMap.mulRight_eq_one_iff]
    tfae_finish
  · simp_all

/--
@isnad1 id=iff.0h4v.s9.c8ccffd4e442 from=translated src=- shape=f3751fd7 vocab=f6499f97
-/
theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight {H₁ : Type _} [Semiring H₁] [Algebra R H₁]
    (x : H₁) (p : Prop) [Decidable p] :
    LinearMap.mulLeft R x = ite p 1 0 ↔ LinearMap.mulRight R x = ite p 1 0 :=
  List.TFAE.out (@LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae R _ H₁ _ _ x p _) 1 2

/--
@isnad1 id=eq.0h4v.s8.82b6752fe308 from=translated src=- shape=f01227d1 vocab=08cb5ade
-/
theorem LinearMap.mulRight_smul (x : H₁) (α : R) :
    LinearMap.mulRight R (α • x) = α • LinearMap.mulRight R x :=
  rmul.map_smul _ _

/--
@isnad1 id=eq.0h4v.s8.94246ca9c8c2 from=translated src=- shape=f01227d1 vocab=6a991f94
-/
theorem LinearMap.mulLeft_smul (x : H₁) (α : R) :
    LinearMap.mulLeft R (α • x) = α • LinearMap.mulLeft R x :=
  lmul.map_smul _ _

/--
@isnad1 id=iff.0h6v.s8.388abca766e1 from=translated src=- shape=b667209e vocab=9933808a
-/
theorem LinearMap.mulLeft_comp_inj {H₁ H₂ : Type _} [Semiring H₁] [Module R H₁] [AddCommMonoid H₂]
    [Module R H₂] [SMulCommClass R H₁ H₁] (f g : H₁ →ₗ[R] H₂) (x : H₁)
    [Invertible x] : f ∘ₗ LinearMap.mulLeft R x = g ∘ₗ LinearMap.mulLeft R x ↔ f = g := by
  refine ⟨?_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  intro h y
  specialize h (⅟ x * y)
  simp_all

/--
@isnad1 id=iff.0h5v.s8.337b1d76bc47 from=translated src=- shape=e71b996e vocab=adc91dfa
-/
theorem LinearMap.mulLeft_apply_inj {H₁ : Type _} [Semiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁]
    (x : H₁) [Invertible x] (y z : H₁) :
    LinearMap.mulLeft R x y = LinearMap.mulLeft R x z ↔ y = z :=
  IsUnit.mul_right_inj (isUnit_of_invertible x)

/--
@isnad1 id=eq.0h3v.s9.f8439fd2a26a from=translated src=- shape=f1e12ab8 vocab=bc2dcc0d
-/
theorem lmul_op {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : Aᵐᵒᵖ) :
    lmul x = (rmul (x.unop) : A →ₗ[R] A).op :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.8ee3549b2ee9 from=translated src=- shape=3e4b654a vocab=696e2512
-/
theorem lmul_op' {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : A) :
    lmul (MulOpposite.op x) = (rmul x : A →ₗ[R] A).op :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.3ecd2e6032f4 from=translated src=- shape=3e4b654a vocab=696e2512
-/
theorem rmul_op' {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : A) :
    rmul (MulOpposite.op x) = (lmul x : A →ₗ[R] A).op :=
  rfl
