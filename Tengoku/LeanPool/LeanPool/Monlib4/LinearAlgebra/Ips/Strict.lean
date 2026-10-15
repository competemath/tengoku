/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# Strict tensor product (wip)
-/

@[expose] public section

variable {R E F G : Type _} [CommSemiring R] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module R E] [Module R F] [Module R G]

open scoped TensorProduct

@[reducible, instance]
noncomputable def TensorProduct.assocHasCoe :
  CoeFun ((E ⊗[R] F) ⊗[R] G) (fun _ ↦ E ⊗[R] (F ⊗[R] G))
    where coe x := TensorProduct.assoc R E F G x

@[reducible, instance]
noncomputable def TensorProduct.assocSymmHasCoe :
  CoeFun (E ⊗[R] (F ⊗[R] G)) (fun _ ↦ (E ⊗[R] F) ⊗[R] G)
    where coe x := (TensorProduct.assoc R E F G).symm x

/--
@isnad1 id=eq.0h7v.s10.8d4f2939a5db from=translated src=- shape=867a53cf vocab=d970c9bf
-/
theorem TensorProduct.assoc_tmul_coe (a : E) (b : F) (c : G) :
    (a ⊗ₜ[R] b) ⊗ₜ[R] c = ↑(a ⊗ₜ[R] (b ⊗ₜ[R] c)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s11.8d8371b1139d from=translated src=- shape=d4479a0c vocab=6bec36b6
-/
theorem TensorProduct.assoc_coe_coe (a : (E ⊗[R] F) ⊗[R] G) :
    a = ↑(a : E ⊗[R] (F ⊗[R] G)) := by simp only [LinearEquiv.symm_apply_apply]

/--
@isnad1 id=eq.0h7v.s10.2047104ad21f from=translated src=- shape=f47eb2e0 vocab=636e5e60
-/
theorem TensorProduct.tmul_assoc_coe (a : E) (b : F) (c : G) :
    a ⊗ₜ[R] (b ⊗ₜ[R] c) = ↑((a ⊗ₜ[R] b) ⊗ₜ[R] c) :=
  rfl

/--
@isnad1 id=eq.0h5v.s11.762df826aeea from=translated src=- shape=855d7787 vocab=6bec36b6
-/
theorem TensorProduct.coe_coe_assoc (a : E ⊗[R] (F ⊗[R] G)) :
    a = ↑(a : (E ⊗[R] F) ⊗[R] G) := by simp only [LinearEquiv.apply_symm_apply]

@[reducible, instance]
noncomputable def TensorProduct.lidHasCoe :
    CoeFun (R ⊗[R] E) (fun _ => E) where
  coe x := TensorProduct.lid R E x

@[reducible, instance]
noncomputable def TensorProduct.ridHasCoe :
    CoeFun (E ⊗[R] R) (fun _ => E) where
  coe x := TensorProduct.rid R E x

@[reducible, instance]
noncomputable def TensorProduct.lidSymmHasCoe :
    Coe E (R ⊗[R] E) where
  coe x := (TensorProduct.lid R E).symm x

@[reducible, instance]
noncomputable def TensorProduct.ridSymmHasCoe :
    Coe E (E ⊗[R] R) where
  coe x := (TensorProduct.rid R E).symm x

/--
@isnad1 id=eq.0h4v.s9.34b1941169de from=translated src=- shape=3f49818b vocab=5d0143ea
-/
theorem TensorProduct.lid_coe (x : E) (r : R) :
  (r ⊗ₜ[R] x : R ⊗[R] E) = r • x :=
  by simp only [lid_symm_apply, smul_tmul', smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h4v.s9.8ec72d40b3f4 from=translated src=- shape=cd1d7242 vocab=47523166
-/
theorem TensorProduct.rid_coe (x : E) (r : R) : (x ⊗ₜ[R] r) = r • x :=
  by simp only [rid_symm_apply, smul_tmul', smul_tmul, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h3v.s8.25ef0c07c60b from=translated src=- shape=f4c461b9 vocab=4ec28973
-/
theorem TensorProduct.lid_symm_coe (x : E) : (x : R ⊗[R] E) = (1 : R) ⊗ₜ[R] x :=
  rfl

/--
@isnad1 id=eq.0h3v.s8.086d0abfbdbc from=translated src=- shape=f4164246 vocab=27cc4b4b
-/
theorem TensorProduct.rid_symm_coe (x : E) : (x : E ⊗[R] R) = x ⊗ₜ[R] (1 : R) :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.34b1941169de from=translated src=- shape=3f49818b vocab=5d0143ea
-/
theorem TensorProduct.lid_coe' (x : E) (r : R) : r ⊗ₜ[R] x = r • x := by
  rw [TensorProduct.lid_symm_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h4v.s9.8ec72d40b3f4 from=translated src=- shape=cd1d7242 vocab=47523166
-/
theorem TensorProduct.rid_coe' (x : E) (r : R) : x ⊗ₜ[R] r = r • x := by
  rw [TensorProduct.rid_symm_coe, TensorProduct.smul_tmul', TensorProduct.smul_tmul, smul_eq_mul,
    mul_one]

/--
@isnad1 id=eq.0h3v.s10.bc3182a7e54c from=translated src=- shape=e11de22c vocab=b3dde18b
-/
theorem TensorProduct.lid_coe_rid_coe (x : E) :
  (x : R ⊗[R] E) = (x : E ⊗[R] R) := by simp only [LinearEquiv.apply_symm_apply]

@[reducible, instance]
noncomputable def funTensorProductAssocHasCoe {A : Type _} :
    CoeFun (((E ⊗[R] F) ⊗[R] G → A)) (fun _ => E ⊗[R] (F ⊗[R] G) → A)
    where coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductAssocHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe ((E ⊗[R] F) ⊗[R] G →ₗ[R] A) (E ⊗[R] (F ⊗[R] G) →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      (((TensorProduct.assoc R E F G).symm :
          E ⊗[R] (F ⊗[R] G) ≃ₗ[R] (E ⊗[R] F) ⊗[R] G) :
        E ⊗[R] (F ⊗[R] G) →ₗ[R] (E ⊗[R] F) ⊗[R] G)

@[reducible, instance]
noncomputable def funTensorProductAssocHasCoe' {A : Type _} :
    Coe (E ⊗[R] (F ⊗[R] G) → A) ((E ⊗[R] F) ⊗[R] G → A)
    where coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductAssocHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] (F ⊗[R] G) →ₗ[R] A) ((E ⊗[R] F) ⊗[R] G →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      ((TensorProduct.assoc R E F G :
          (E ⊗[R] F) ⊗[R] G ≃ₗ[R] E ⊗[R] (F ⊗[R] G)) :
        (E ⊗[R] F) ⊗[R] G →ₗ[R] E ⊗[R] (F ⊗[R] G))

@[reducible, instance]
noncomputable def funLidHasCoe {A : Type _} :
    CoeFun (R ⊗[R] E → A) (fun _ ↦ E → A) where
  coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductLidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (R ⊗[R] E →ₗ[R] A) (E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.lid R E).symm

@[reducible, instance]
noncomputable def funLidHasCoe' {A : Type _} :
    Coe (E → A) (R ⊗[R] E → A) where
  coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductLidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (R ⊗[R] E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.lid R E)

@[reducible, instance]
noncomputable def funRidHasCoe {A : Type _} :
    CoeFun (E ⊗[R] R → A) (fun _ => E → A) where
  coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductRidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] R →ₗ[R] A) (E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.rid R E).symm

@[reducible, instance]
noncomputable def funRidHasCoe' {A : Type _} :
    Coe (E → A) (E ⊗[R] R → A) where
  coe f x := f x

@[reducible, instance]
noncomputable def LinearMap.tensorProductRidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (E ⊗[R] R →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.rid R E)

/--
@isnad1 id=eq.0h4v.s9.5b5c4b7b8931 from=translated src=- shape=1b659d9c vocab=5d9d88f1
-/
theorem LinearMap.lid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : R ⊗[R] E →ₗ[R] A) := by
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

/--
@isnad1 id=eq.0h4v.s9.e246e3fcbb4b from=translated src=- shape=82591bc6 vocab=5d9d88f1
-/
theorem LinearMap.lid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : R ⊗[R] E →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

/--
@isnad1 id=eq.0h4v.s9.44fc80150520 from=translated src=- shape=ceb723b0 vocab=f526bbe8
-/
theorem LinearMap.rid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : E ⊗[R] R →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

/--
@isnad1 id=eq.0h4v.s9.27d7d1add2d6 from=translated src=- shape=4c2b746b vocab=f526bbe8
-/
theorem LinearMap.rid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E ⊗[R] R →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
