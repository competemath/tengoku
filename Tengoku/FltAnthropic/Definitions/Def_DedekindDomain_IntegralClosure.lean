import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Mathlib_RingTheory_Localization_BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

section

namespace IsDedekindDomain.HeightOneSpectrum

section BaseChange

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L]

variable (v : HeightOneSpectrum A)

variable {A} in

def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.under A = v}

lemma ramificationIdx_ne_zero (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) :
    Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (under A w).3) w.2 Ideal.map_comap_le

include K L in
omit [IsDedekindDomain A] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
lemma isTorsionFree [IsDomain B] : Module.IsTorsionFree A B := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  infer_instance

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in

theorem Extension.finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
  have := isTorsionFree A K L B
  rw [Extension, ← Set.coe_ofPred]
  rw [@Set.finite_coe_iff]
  have := primesOver_finite v.asIdeal B
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ ?_
  · refine Set.Finite.subset this ?_
    simp only [Set.subset_def, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rintro w rfl
    simp only [Ideal.primesOver, Set.mem_ofPred_eq, isPrime, true_and]
    constructor
    simp [Ideal.under_def, under]
  · intro x hx y hy hxy
    rwa [← @HeightOneSpectrum.ext_iff] at hxy

@[reducible]
noncomputable def Extension.fintype : Fintype (Extension B v) :=
  have := Extension.finite A K L B v
  Fintype.ofFinite <| Extension B v

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in
theorem preimage_comap_finite (S : Set (HeightOneSpectrum A)) (hS : S.Finite) :
    ((under A : HeightOneSpectrum B → HeightOneSpectrum A) ⁻¹' S).Finite := by
  rw [← Set.biUnion_preimage_singleton (under A) S]
  exact Set.Finite.biUnion' hS <| fun v _ ↦ Extension.finite A K L B v

noncomputable def preimageComapFinset (S : Finset (HeightOneSpectrum A)) :
    Finset (HeightOneSpectrum B) :=
  Set.Finite.toFinset <| preimage_comap_finite A K L B S S.finite_toSet

end BaseChange

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

noncomputable def LinearEquivTensorProduct :
    L ≃ₗ[K] K ⊗[A] B :=
  let f := LocalizedModule.equivTensorProduct (nonZeroDivisors A) B
  have := IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule (nonZeroDivisors A) (IsScalarTower.toAlgHom A B L).toLinearMap :=
    inferInstance
  let g : LocalizedModule (nonZeroDivisors A) B ≃ₗ[A] L := @IsLocalizedModule.iso
      _ _ (nonZeroDivisors A) _ _ _ _ _ _ (IsScalarTower.toAlgHom A B L) this
  let h := TensorProduct.congr (Localization.algEquiv (nonZeroDivisors A) K) (LinearEquiv.refl A B)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K
    <| g.symm.trans (f.restrictScalars A) |>.trans h

variable (M : Type*) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]

noncomputable def linearEquivTensorProductModule : L ⊗[K] M ≃ₗ[A] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[A] L ⊗[A] M := IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K L M
    |>.restrictScalars A
  let f₂ : L ≃ₗ[A] B ⊗[A] K := LinearEquivTensorProduct A K L B
    |>.restrictScalars A
    |>.trans (TensorProduct.comm A K B)
  let f₃ : L ⊗[A] M ≃ₗ[A] (B ⊗[A] K) ⊗[A] M := TensorProduct.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[A] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.assoc A B K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[A] B ⊗[A] M := TensorProduct.congr (LinearEquiv.refl A B)
    (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃ |>.trans f₄ |>.trans f₅

end IsDedekindDomain

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]
