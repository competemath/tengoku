import Tengoku.Aintlib.ModularCurves.ForMathlib.AffinePatchBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Naturality of affine patch base change

The tensor-product description of sections on a pulled-back affine source
patch is compatible with restriction to a smaller affine patch.
-/

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

private theorem pullbackPreimageIsoPullbackRestrict_hom_fst
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens) :
    (pullbackPreimageIsoPullbackRestrict f t U).hom ≫
        pullback.fst (U.ι ≫ f) t =
      pullback.fst f t ∣_ U := by
  simp [pullbackPreimageIsoPullbackRestrict]
  rfl

private theorem pullbackPreimageIsoPullbackRestrict_hom_snd
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens) :
    (pullbackPreimageIsoPullbackRestrict f t U).hom ≫
        pullback.snd (U.ι ≫ f) t =
      (pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t := by
  simp [pullbackPreimageIsoPullbackRestrict]
  rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst]

/-- Restriction from `U` to `V` as an algebra map over the global sections of
the affine base.-/
noncomputable def affinePatchRestrictionAlgHom
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : X.Opens} (hVU : V ≤ U) :
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      ((V.ι ≫ f).appTop.hom).toAlgebra
    Γ(U.toScheme, (⊤ : U.toScheme.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))]
      Γ(V.toScheme, (⊤ : V.toScheme.Opens)) := by
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    ((V.ι ≫ f).appTop.hom).toAlgebra
  exact
    { toRingHom := (X.homOfLE hVU).appTop.hom
      commutes' := fun r => by
        change (X.homOfLE hVU).appTop ((U.ι ≫ f).appTop r) =
          (V.ι ≫ f).appTop r
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
        simp }

/-- Restriction on a source patch tensored with the identity on the new base.-/
noncomputable def affinePatchRestrictionTensorHom
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
    {U V : X.Opens} (hVU : V ≤ U) :
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      ((V.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    CommRingCat.of
        (Γ(U.toScheme, (⊤ : U.toScheme.Opens)) ⊗[Γ(S, (⊤ : S.Opens))]
          Γ(T, (⊤ : T.Opens))) ⟶
      CommRingCat.of
        (Γ(V.toScheme, (⊤ : V.toScheme.Opens)) ⊗[Γ(S, (⊤ : S.Opens))]
          Γ(T, (⊤ : T.Opens))) := by
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    ((V.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  exact CommRingCat.ofHom
    (Algebra.TensorProduct.map (affinePatchRestrictionAlgHom f hVU)
      (AlgHom.id Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)))).toRingHom

/-- The left tensor generator pulls a function on `U` back along
`U ×_S T ⟶ U`.-/
theorem pullbackPreimageΓIsoTensor_inv_includeLeft
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := Γ(S, (⊤ : S.Opens)))
          (A := Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
          (B := Γ(T, (⊤ : T.Opens)))) ≫
        (pullbackPreimageΓIsoTensor f t U hU).inv =
      (pullback.fst f t ∣_ U).appTop ≫
        (pullback.fst f t ⁻¹ᵁ U).topIso.hom := by
  letI : IsAffine U.toScheme := hU
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  rw [pullbackPreimageΓIsoTensor_inv]
  rw [← fst_appTop_affineKunnethΓ (U.ι ≫ f) t rfl rfl]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop,
    pullbackPreimageIsoPullbackRestrict_hom_fst]

/-- The right tensor generator pulls a function on `T` back along
`U ×_S T ⟶ T`.-/
theorem pullbackPreimageΓIsoTensor_inv_includeRight
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    CommRingCat.ofHom ((Algebra.TensorProduct.includeRight
          (R := Γ(S, (⊤ : S.Opens)))
          (A := Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
          (B := Γ(T, (⊤ : T.Opens)))).toRingHom) ≫
        (pullbackPreimageΓIsoTensor f t U hU).inv =
      ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop ≫
        (pullback.fst f t ⁻¹ᵁ U).topIso.hom := by
  letI : IsAffine U.toScheme := hU
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  rw [pullbackPreimageΓIsoTensor_inv]
  rw [← snd_appTop_affineKunnethΓ (U.ι ≫ f) t rfl rfl]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop,
    pullbackPreimageIsoPullbackRestrict_hom_snd]

end AlgebraicGeometry
