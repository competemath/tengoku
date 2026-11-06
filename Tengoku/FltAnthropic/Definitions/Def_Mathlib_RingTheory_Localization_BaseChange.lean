import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

section

namespace IsLocalization

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  (M₁ : Type*) [AddCommMonoid M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]

/--
@isnad1 id=eq.0h5v.s9.1605bbdf3477 from=translated src=- shape=1e3d3145 vocab=9e2938af
-/
@[simp]
lemma moduleLid_symm_apply (m : M₁) : (moduleLid S A M₁).symm m = 1 ⊗ₜ[R] m := rfl

variable (M₂ : Type*) [AddCommMonoid M₂] [Module R M₂] [Module A M₂] [IsScalarTower R A M₂]

/--
@isnad1 id=eq.0h7v.s9.1edc8610c4ae from=translated src=- shape=d8c4bddc vocab=4b829a9e
-/
@[simp]
lemma map_moduleTensorEquiv_tmul (m₁ : M₁) (m₂ : M₂) :
    moduleTensorEquiv S A M₁ M₂ (m₁ ⊗ₜ[A] m₂) = m₁ ⊗ₜ[R] m₂ := rfl

/--
@isnad1 id=eq.0h7v.s9.46b7e3a41e82 from=translated src=- shape=d4ac0527 vocab=305e4b92
-/
@[simp]
lemma map_moduleTensorEquiv_symm_tmul (m₁ : M₁) (m₂ : M₂) :
    (moduleTensorEquiv S A M₁ M₂).symm (m₁ ⊗ₜ[R] m₂) = m₁ ⊗ₜ[A] m₂ := rfl

end

section

open TensorProduct

variable {A : Type*} [CommSemiring A] (S : Submonoid A)
  (B : Type*) [CommSemiring B] [Algebra A B]
  (K : Type*) [CommSemiring K] [Algebra A K] [IsLocalization S K]
  (L : Type*) [CommSemiring L] [Algebra B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalizedModule (M := B) (M' := L) S (Algebra.linearMap B L)]
  (M : Type*) [AddCommMonoid M] [Module K M]
  (P : Type*) [AddCommMonoid P] [Module K P]

@[simps!]
noncomputable def leftModuleTensorEquiv {R : Type*} (M' : Type*)
    [Semiring M'] [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁] [Module A M₂]
    [SMulCommClass A M' M₁] [SMulCommClass R M' M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    M₁ ⊗[A] M₂ ≃ₗ[M'] M₁ ⊗[R] M₂ where
  __ := IsLocalization.moduleTensorEquiv S A M₁ M₂
  map_smul' r x := by
    induction x with
    | zero => simp
    | tmul m₁ m₂ => simp [TensorProduct.smul_tmul']
    | add => simp_all

end

end IsLocalization
