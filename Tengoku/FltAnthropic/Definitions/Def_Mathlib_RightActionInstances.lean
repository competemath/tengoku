import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

section

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

/--
@isnad1 id=eq.0h5v.s10.60d8bd3cece3 from=translated src=- shape=63005747 vocab=f77389df
-/
@[simp]
lemma smul_def (r : S) (m : M ⊗[R] S) :
    r • m = (TensorProduct.comm _ _ _).symm (r • (TensorProduct.comm _ _ _ m)) := rfl

scoped instance : Module S (M ⊗[R] S) where
  one_smul x := by simp_rw [smul_def, one_smul, (TensorProduct.comm R M S).symm_apply_apply]
  mul_smul a b x := by simp_rw [smul_def, mul_smul, (TensorProduct.comm R M S).apply_symm_apply]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

scoped instance : Algebra S (B ⊗[R] S) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' s bs := by
    induction bs with
    | zero => simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul x y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y _ _ =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' s bs := by
    induction bs with
    | zero => simp only [smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero]
    | tmul b s =>
        simp only [smul_def, TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [TensorProduct.smul_tmul']
        simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, smul_add, mul_add]

/--
@isnad1 id=eq.0h4v.s8.277e67c9e7b9 from=translated src=- shape=447f4e80 vocab=a1dd6dd5
-/
@[simp] lemma algebraMap_eval (s : S) : algebraMap S (B ⊗[R] S) s = 1 ⊗ₜ s := rfl

def Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := _root_.Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

variable {A B} in
/--
@isnad1 id=eq.0h5v.s8.0195f4d1903b from=translated src=- shape=729da1f7 vocab=ede27be2
-/
@[simp] lemma Algebra.TensorProduct.comm_apply_tmul (a : A) (b : B) :
    Algebra.TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a := by
  rfl

/--
@isnad1 id=eq.0h5v.s9.c2d06b904074 from=translated src=- shape=201597a3 vocab=2bf911be
-/
@[simp] lemma Algebra.TensorProduct.comm_symm_apply_tmul (b : B) (a : A) :
    (Algebra.TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := by
    induction am with
    | zero => simp only [smul_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      map_zero, RingHom.id_apply]
    | tmul x y =>
        simp only [smul_tmul', smul_eq_mul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, comm_tmul, RingHom.id_apply, smul_def, comm_symm_tmul]
    | add x y hx hy =>
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply, smul_def, smul_add, map_add]

variable {A N} in
/--
@isnad1 id=eq.0h5v.s9.a1e41fc4e1d5 from=translated src=- shape=15394430 vocab=312e3859
-/
@[simp] lemma Module.TensorProduct.comm_apply_tmul (a : A) (m : M) :
    Module.TensorProduct.comm R A M (a ⊗ₜ m) = m ⊗ₜ a := rfl

/--
@isnad1 id=eq.0h5v.s9.136e712444ae from=translated src=- shape=9615d891 vocab=a6e85c31
-/
@[simp] lemma Module.TensorProduct.comm_symm_apply_tmul (m : M) (a : A) :
    (Module.TensorProduct.comm R A M).symm (m ⊗ₜ a) = a ⊗ₜ m := rfl

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := by simp

@[nolint unusedArguments]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    TopologicalSpace (M ⊗[R] A) :=
  moduleTopology A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [Module.Finite R M] :
  IsModuleTopology A (M ⊗[R] A) := ⟨rfl⟩

noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

/--
@isnad1 id=eq.0h3v.s8.d4242910c106 from=translated src=- shape=7b9c0b9c vocab=03ed7641
-/
@[simp]
lemma LinearMap.baseChange_id (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V]
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.baseChange R V V A .id = .id := by
  ext
  simp

/--
@isnad1 id=eq.0h7v.s9.94bc67ac6c7f from=translated src=- shape=0de2c8a9 vocab=fb08d2c1
-/
theorem LinearMap.baseChange_comp (R : Type*) [CommRing R]
    (U V W : Type*) [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (A : Type*) [CommRing A] [Algebra R A]
    (φ : U →ₗ[R] V) (ψ : V →ₗ[R] W) :
    LinearMap.baseChange R V W A ψ ∘ₗ LinearMap.baseChange R U V A φ =
    LinearMap.baseChange R U W A (ψ ∘ₗ φ) := by
  ext
  simp [_root_.LinearMap.baseChange_comp]

noncomputable abbrev LinearEquiv.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V ≃ₗ[R] W) : V ⊗[R] A ≃ₗ[A] W ⊗[R] A where
  __ := LinearMap.baseChange _ _ _ _ φ.toLinearMap
  invFun := LinearMap.baseChange _ _ _ _ φ.symm.toLinearMap
  left_inv := by
    intro x
    calc
    _ = (LinearMap.baseChange R W V A φ.symm ∘ₗ LinearMap.baseChange R V W A φ) x := rfl
    _ = _ := by simp [LinearMap.baseChange_comp]
  right_inv := by
    intro y
    change ((LinearMap.baseChange R V W A φ) ∘ₗ (LinearMap.baseChange R W V A φ.symm)) y = _
    simp [LinearMap.baseChange_comp]

noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := by simp

def Algebra.TensorProduct.basis {R : Type*} (A : Type*) {M : Type*} {ι : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) :
    Module.Basis ι A (M ⊗[R] A) :=
  (_root_.Algebra.TensorProduct.basis A b).map (Module.TensorProduct.comm R A M)

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]
    [AddCommGroup M] [Module R M]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    IsTopologicalAddGroup (M ⊗[R] A) := IsModuleTopology.topologicalAddGroup A (M ⊗[R] A)

end ring

end TensorProduct.RightActions
