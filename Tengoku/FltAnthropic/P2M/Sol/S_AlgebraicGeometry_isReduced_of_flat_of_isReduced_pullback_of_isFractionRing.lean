import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace P2mFlatReduced

/--
@isnad1 id=isreduce.0h3v.s8.b5921b432824 from=translated src=- shape=01bae72d vocab=0205a5ec
-/
theorem isReduced_of_flat_of_isReduced_tensor
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A] [IsReduced (K ⊗[R] A)] :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  have h1 : IsNilpotent ((1 : K) ⊗ₜ[R] a) := by
    have := ha.map (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A))
    simpa [Algebra.TensorProduct.includeRight_apply] using this
  have h2 : ((1 : K) ⊗ₜ[R] a) = 0 := h1.eq_zero
  have h3 : (TensorProduct.mk R K A 1) a = 0 := h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (TensorProduct.mk R K A 1)).mp h3
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) s.2
  exact hreg (show (s : R) • a = (s : R) • 0 by rw [smul_zero, ← Submonoid.smul_def, hs])

/--
@isnad1 id=isreduce.0h3v.s6.b61ae4a34014 from=translated src=- shape=0751dee6 vocab=5db25f54
-/
theorem isReduced_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) [IsReduced A] :
    IsReduced B :=
  isReduced_of_injective e.symm.toRingHom e.symm.injective

/--
@isnad1 id=isreduce.0h6v.s6.89c84e0324e9 from=translated src=- shape=6f8ae2bf vocab=15290708
-/
theorem isReduced_affine
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (Y : Scheme.{u}) [IsAffine Y] (u₀ : Y ⟶ X) [IsOpenImmersion u₀] :
    IsReduced Y := by
  set sK := Spec.map (CommRingCat.ofHom (algebraMap R K)) with hsK
  let A : CommRingCat.{u} := Γ(Y, ⊤)
  let u : Spec A ⟶ X := Y.isoSpec.inv ≫ u₀
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (u ≫ f)
  have hφ : Spec.map φ = u ≫ f := Spec.map_preimage _

  letI : Algebra R A := φ.hom.toAlgebra
  haveI : Module.Flat R A := by
    have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    have hflat : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
    exact hflat

  haveI : IsReduced (pullback (u ≫ f) sK) := by
    let e := pullbackRightPullbackFstIso f sK u
    haveI : IsReduced (pullback u (pullback.fst f sK)) :=
      isReduced_of_isOpenImmersion (pullback.snd u (pullback.fst f sK))
    exact isReduced_of_isOpenImmersion e.inv
  haveI : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) sK) := by
    have hg : Spec.map (CommRingCat.ofHom (algebraMap R A)) = u ≫ f := hφ
    exact isReduced_of_isOpenImmersion (pullback.congrHom hg rfl).hom
  haveI : IsReduced (Spec (CommRingCat.of (A ⊗[R] K))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso R A K).inv
  haveI : _root_.IsReduced (A ⊗[R] K) := (affine_isReduced_iff (CommRingCat.of (A ⊗[R] K))).mp inferInstance
  haveI : _root_.IsReduced (K ⊗[R] A) :=
    isReduced_of_ringEquiv (Algebra.TensorProduct.comm R A K).toRingEquiv
  haveI : _root_.IsReduced A := isReduced_of_flat_of_isReduced_tensor (R := R) K A
  haveI : _root_.IsReduced Γ(Y, ⊤) := this
  exact isReduced_of_isAffine_isReduced Y

end P2mFlatReduced

open P2mFlatReduced in

/--
@isnad1 id=isreduce.0h4v.s6.a6bb5484a7b0 from=translated src=- shape=8df6b58c vocab=6ca5177f
-/
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i =>
    isReduced_affine K f (X.affineCover.X i) (X.affineCover.f i)
  exact IsReduced.of_openCover (𝒰 := X.affineCover)
