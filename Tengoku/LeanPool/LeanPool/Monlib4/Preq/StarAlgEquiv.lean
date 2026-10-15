/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
 # Some stuff on star algebra equivalences

 This file contains some obvious definitions and lemmas on star algebra equivalences.
-/

@[expose] public section

/--
@isnad1 id=iff.0h7v.s8.b799232258a2 from=translated src=- shape=d8aa011b vocab=88937f89
-/
theorem AlgEquiv.comp_inj {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : B ≃ₐ[R] C) (S T : A →ₗ[R] B) :
    f.toLinearMap ∘ₗ S = f.toLinearMap ∘ₗ T ↔ S = T := by
  simp_all

/--
@isnad1 id=iff.0h7v.s8.9fbb155c9897 from=translated src=- shape=b5ad5c61 vocab=88937f89
-/
theorem AlgEquiv.inj_comp {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : C ≃ₐ[R] A) (S T : A →ₗ[R] B) :
    S ∘ₗ f.toLinearMap = T ∘ₗ f.toLinearMap ↔ S = T := by
  simp_all

/-- The linear map underlying a star algebra equivalence. -/
@[simps]
def StarAlgEquiv.toLinearMap {R A B : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : A →ₗ[R] B where
    toFun x := f x
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_smul, RingHom.id_apply]

/--
@isnad1 id=injectiv.0h4v.s6.e3f7bd04bc90 from=translated src=- shape=7202a07a vocab=fa494ce3
-/
theorem StarAlgEquiv.injective {R A B : Type _} [Add A] [Add B] [Mul A] [Mul B]
  [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : Function.Injective f :=
EquivLike.injective f

/--
@isnad1 id=iff.0h7v.s8.5798c8dcd1ee from=translated src=- shape=a461d003 vocab=67b686ac
-/
theorem StarAlgEquiv.comp_inj {R A B C : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [AddCommMonoid C] [Mul B] [Mul C] [Module R A] [Module R B] [Module R C]
  [Star B] [Star C]
  (f : B ≃⋆ₐ[R] C) (S T : A →ₗ[R] B) :
    f.toLinearMap ∘ₗ S = f.toLinearMap ∘ₗ T ↔ S = T := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
    f.injective.eq_iff]

/--
@isnad1 id=iff.0h7v.s8.7f840d81186a from=translated src=- shape=71d788d2 vocab=67b686ac
-/
theorem StarAlgEquiv.inj_comp {R A B C : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [AddCommMonoid C] [Mul A] [Mul C] [Module R A] [Module R B] [Module R C]
  [Star A] [Star C] (f : C ≃⋆ₐ[R] A) (S T : A →ₗ[R] B) :
    S ∘ₗ f.toLinearMap = T ∘ₗ f.toLinearMap ↔ S = T := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply] at h ⊢
  intro x
  specialize h (f.symm x)
  simp_all

/-- The linear equivalence underlying a star algebra equivalence. -/
@[simps]
def StarAlgEquiv.toLinearEquiv {R A B : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : A ≃ₗ[R] B where
    toFun x := f x
    invFun x := f.symm x
    left_inv x := by simp only [symm_apply_apply]
    right_inv x := by simp only [apply_symm_apply]
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_smul, RingHom.id_apply]

/--
@isnad1 id=eq.1h4v.s7.014b563f2cec from=translated src=- shape=9fcc5fbd vocab=72f77437
-/
@[simp]
theorem StarAlgEquiv.ofAlgEquiv_coe {R A B : Type _}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B]
    (f : A ≃ₐ[R] B) (hf : ∀ x : A, f (star x) = star (f x)) :
    ⇑(StarAlgEquiv.ofAlgEquiv f hf) = f :=
  rfl

/--
@isnad1 id=eq.1h4v.s8.7baad853ed1d from=translated src=- shape=e44dcbc4 vocab=0b3fa545
-/
theorem StarAlgEquiv.ofAlgEquiv_symm_coe {R A B : Type _}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B]
    (f : A ≃ₐ[R] B) (hf : ∀ x : A, f (star x) = star (f x)) :
    ⇑(StarAlgEquiv.ofAlgEquiv f hf).symm = f.symm :=
  rfl

/--
@isnad1 id=iff.0h7v.s8.0be3777ffbce from=translated src=- shape=e528868c vocab=9d40a1af
-/
theorem StarAlgEquiv.comp_eq_iff {R E₁ E₂ E₃ : Type _} [CommSemiring R]
    [AddCommMonoid E₁] [AddCommMonoid E₂] [AddCommMonoid E₃]
    [Module R E₁] [Module R E₂] [Module R E₃] [Star E₁] [Star E₂] [Mul E₁] [Mul E₂]
    (f : E₁ ≃⋆ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
    x ∘ₗ f.toLinearMap = y ↔ x = y ∘ₗ f.symm.toLinearMap := by
  constructor
  · intro h
    ext1
    rw [← h]
    simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
      StarAlgEquiv.apply_symm_apply]
  · rintro rfl
    ext1
    simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply, StarAlgEquiv.symm_apply_apply]

/--
@isnad1 id=iff.0h5v.s6.e1f2f7a9e9ce from=translated src=- shape=fabca646 vocab=1d037ddb
-/
theorem AlgEquiv.map_eq_zero_iff {R E₁ E₂ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [Algebra R E₁] [Algebra R E₂] (f : E₁ ≃ₐ[R] E₂) (x : E₁) : f x = 0 ↔ x = 0 :=
  RingEquiv.map_eq_zero_iff f.toRingEquiv

/--
@isnad1 id=iff.0h5v.s7.f252f69cf035 from=translated src=- shape=0b2fb812 vocab=bb3698e5
-/
theorem StarAlgEquiv.map_eq_zero_iff {R A B : Type _}
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) (x : A) :
    f x = 0 ↔ x = 0 :=
  RingEquiv.map_eq_zero_iff f.toRingEquiv

/--
@isnad1 id=iff.0h5v.s5.5f82f685c512 from=translated src=- shape=4c38cdf8 vocab=4ccd2c0f
-/
theorem IsIdempotentElem.mulEquiv {H₁ H₂ : Type _} [Mul H₁] [Mul H₂]
  -- (f : H₁ ≃* H₂)
  {F : Type*} [EquivLike F H₁ H₂] [MulEquivClass F H₁ H₂] {f : F} {x : H₁} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x := by
  simp_rw [IsIdempotentElem, ← _root_.map_mul]
  exact EmbeddingLike.apply_eq_iff_eq f

/--
@isnad1 id=iff.0h5v.s6.7cbe99de117c from=translated src=- shape=304d4a29 vocab=0d221e9c
-/
theorem IsIdempotentElem.algEquiv {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂]
    [Algebra R H₁] [Algebra R H₂] (f : H₁ ≃ₐ[R] H₂) {x : H₁} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
IsIdempotentElem.mulEquiv

/--
@isnad1 id=iff.0h5v.s6.f2ead044c055 from=translated src=- shape=b43a0c2b vocab=1f1b56c1
-/
theorem IsIdempotentElem.starAlgEquiv {R A B : Type _}
   [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A] [Star B]
   (f : A ≃⋆ₐ[R] B) {x : A} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
IsIdempotentElem.mulEquiv

lemma _root_.isIdempotentElem_pi_iff
  {ι : Type*} {A : ι → Type*} [Π i, Mul (A i)] {a : Π i, A i} :
  IsIdempotentElem a ↔ ∀ i, IsIdempotentElem (a i) := by
  simp only [IsIdempotentElem, Pi.mul_def, funext_iff]

theorem AlgEquiv.eq_apply_iff_symm_eq {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {a : B} {b : A} : a = f b ↔ f.symm a = b := by
  have : ∀ e : A ≃ B, a = e b ↔ e.symm a = b := by
    intro e
    rw [← Equiv.apply_eq_iff_eq e, Equiv.apply_symm_apply]
  exact this f

theorem StarAlgEquiv.eq_apply_iff_symm_eq {R A B : Type _}
  [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) {a : B} {b : A} :
    a = f b ↔ f.symm a = b := by
  rw [eq_comm]
  nth_rw 2 [eq_comm]
  exact (Equiv.eq_symm_apply f.toRingEquiv.toEquiv).symm

/--
@isnad1 id=iff.0h6v.s6.26db399b049f from=translated src=- shape=962f1eb2 vocab=1d037ddb
-/
lemma AlgEquiv.apply_eq_iff_eq {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]
  (f : A ≃ₐ[R] B) {x y : A} :
  f x = f y ↔ x = y :=
Equiv.apply_eq_iff_eq f.toEquiv

/--
@isnad1 id=eq.0h4v.s5.dee58d82cfce from=translated src=- shape=03077fa6 vocab=82760ae6
-/
lemma MulEquiv.image_center {F A B : Type*} [Semigroup A] [Semigroup B]
  [EquivLike F A B] [MulEquivClass F A B]
  (f : F) :
  f '' (Set.center A) = Set.center B := by
  let f' : A ≃* B := f
  ext x
  symm
  calc x ∈ Set.center B ↔ ∀ y, y * x = x * y := Semigroup.mem_center_iff
    _ ↔ ∀ y, f'.symm y * f'.symm x = f'.symm x * f'.symm y := by
      simp only [MulEquiv.apply_eq_iff_eq, ← map_mul]
    _ ↔ ∀ y, y * f'.symm x = f'.symm x * y := by
      refine ⟨fun h y => ?_, fun h y => h _⟩
      specialize h (f' y)
      simp_all only [MulEquiv.symm_apply_apply]
    _ ↔ f'.symm x ∈ Set.center A := Semigroup.mem_center_iff.symm
    _ ↔ x ∈ f '' Set.center A := Set.mem_image_equiv.symm

instance
  {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [DistribMulAction R A] [DistribMulAction R B]
  [EquivLike F A B] [NonUnitalAlgHomClass F R A B] :
  MulEquivClass F A B where
  map_mul := MulHomClass.map_mul

/-- Assemble pointwise star algebra equivalences into a star algebra equivalence of dependent
functions. -/
@[simps apply]
def StarAlgEquiv.piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*}
  [(i : ι) → Add (A₁ i)] [(i : ι) → Add (A₂ i)]
  [(i : ι) → Mul (A₁ i)] [(i : ι) → Mul (A₂ i)]
  [(i : ι) → Star (A₁ i)] [(i : ι) → Star (A₂ i)]
  [(i : ι) → SMul R (A₁ i)] [(i : ι) → SMul R (A₂ i)]
  (e : (i : ι) → A₁ i ≃⋆ₐ[R] A₂ i) :
  ((i : ι) → A₁ i) ≃⋆ₐ[R] (i : ι) → A₂ i where
    toFun x j := e j (x j)
    invFun x j := (e j).symm (x j)
    map_add' _ _ := by simp only [Pi.add_apply, map_add]; rfl
    map_mul' _ _ := by simp only [Pi.mul_apply, map_mul]; rfl
    map_star' _ := by simp only [Pi.star_apply, map_star]; rfl
    map_smul' _ _ := by simp only [Pi.smul_apply, map_smul]; rfl
    left_inv _ := by simp only [symm_apply_apply]
    right_inv _ := by simp only [apply_symm_apply]

/--
@isnad1 id=eq.0h6v.s7.645566988622 from=translated src=- shape=9f136280 vocab=2f82c7a9
-/
theorem AlgEquiv.coe_comp
  {R A₁ A₂ A₃ : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂]
  [Semiring A₃] [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  (e : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  e₂.toLinearMap.comp e.toLinearMap = (e.trans e₂).toLinearMap :=
rfl

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
@isnad1 id=eq.0h2v.s6.27f3fa0c75d3 from=translated src=- shape=384b244d vocab=2669360c
-/
theorem AlgEquiv.refl_toLinearMap :
  (AlgEquiv.refl (R := R) (A₁ := A)).toLinearMap = LinearMap.id :=
rfl
/--
@isnad1 id=eq.0h4v.s7.95999527fdfb from=translated src=- shape=dc93b610 vocab=10452993
-/
theorem AlgEquiv.symm_comp_toLinearMap (e : A ≃ₐ[R] B) :
  e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
by simp only [coe_comp, self_trans_symm]; rfl
/--
@isnad1 id=eq.0h4v.s7.2d93611f3a7f from=translated src=- shape=10c658c2 vocab=10452993
-/
theorem AlgEquiv.comp_symm_toLinearMap (e : A ≃ₐ[R] B) :
  e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id :=
by simp only [coe_comp, symm_trans_self]; rfl
