/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite

/-!

# Proper morphisms

A morphism of schemes is proper if it is separated, universally closed and (locally) of finite type.
Note that we don't require quasi-compact, since this is implied by universally closed.

## Main results
- `AlgebraicGeometry.isField_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed over `Spec K`, then `Γ(X, ⊤)` is a field.
- `AlgebraicGeometry.finite_appTop_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
  then `Γ(X, ⊤)` is finite dimensional over `K`.

-/

public section


noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is proper if it is separated, universally closed and locally of finite type. -/
@[mk_iff]
class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f where

/--
@isnad1 id=eq.0h0v.s6.499591b77a35 from=seed src=0 shape=5286e9ff vocab=81dd4466
-/
lemma isProper_eq : @IsProper =
    (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType := by
  ext X Y f
  rw [isProper_iff, ← and_assoc]
  rfl

namespace IsProper

set_option backward.isDefEq.respectTransparency.types false in
instance : MorphismProperty.RespectsIso @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isstable.0h0v.s2.716975415929 from=seed src=0 shape=25b03439 vocab=5ad652a2
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance : MorphismProperty.IsMultiplicative @IsProper := by
  rw [isProper_eq]
  infer_instance

instance [IsProper f] [IsProper g] : IsProper (f ≫ g) where

instance (priority := 900) [IsFinite f] : IsProper f where

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isstable.0h0v.s2.fec8cca56bc4 from=seed src=0 shape=25b03439 vocab=b6493726
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance : IsZariskiLocalAtTarget @IsProper := by
  rw [isProper_eq]
  infer_instance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper g] : IsProper (Limits.pullback.fst f g) where

instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] : IsProper (Limits.pullback.snd f g) where

instance (f : X ⟶ Y) (V : Y.Opens) [IsProper f] : IsProper (f ∣_ V) where

end IsProper

set_option backward.isDefEq.respectTransparency.types false in
lemma IsFinite.eq_isProper_inf_isAffineHom :
    @IsFinite = (@IsProper ⊓ @IsAffineHom : MorphismProperty _) := by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ ↦ inferInstance
  rw [inf_comm, isProper_eq, inf_assoc, ← inf_assoc, this, eq_inf,
    IsIntegralHom.eq_universallyClosed_inf_isAffineHom, inf_assoc, inf_left_comm]

variable {f} in
/--
@isnad1 id=iff.0h3v.s4.975f04949b20 from=seed src=0 shape=2caf7a2f vocab=355b5996
-/
lemma IsFinite.iff_isProper_and_isAffineHom :
    IsFinite f ↔ IsProper f ∧ IsAffineHom f := by
  rw [eq_isProper_inf_isAffineHom]
  rfl

instance (priority := 100) [IsFinite f] : IsProper f :=
  (IsFinite.iff_isProper_and_isAffineHom.mp ‹_›).1

instance : MorphismProperty.HasOfPostcompProperty @UniversallyClosed @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (UniversallyClosed _)

/--
@isnad1 id=universa.0h5v.s5.6386b299a2c2 from=seed src=0 shape=77972de3 vocab=56fb2283
-/
@[stacks 01W6 "(1)"]
lemma UniversallyClosed.of_comp_of_isSeparated [UniversallyClosed (f ≫ g)] [IsSeparated g] :
    UniversallyClosed f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

instance : MorphismProperty.HasOfPostcompProperty @IsProper @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsProper _)

instance [UniversallyClosed f] : UniversallyClosed f.toImage :=
  have : UniversallyClosed (f.toImage ≫ f.imageι) := by simpa
  .of_comp_of_isSeparated _ f.imageι

/--
@isnad1 id=isproper.0h5v.s5.73cd0a387327 from=seed src=0 shape=77972de3 vocab=639b6efb
-/
@[stacks 01W6 "(2)"]
lemma IsProper.of_comp [IsProper (f ≫ g)] [IsSeparated g] : IsProper f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
@isnad1 id=iff.0h5v.s5.200cd1c33b08 from=seed src=0 shape=daa213a1 vocab=ee290b89
-/
lemma IsProper.comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsProper g] :
    IsProper (f ≫ g) ↔ IsProper f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

section GlobalSection

variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f : X ⟶ Y` is universally closed and `Y` is affine,
then the map on global sections is integral.
@isnad1 id=isintegr.0h3v.s10.2b4f76b520b2 from=seed src=0 shape=557d0ee6 vocab=78887613
-/
theorem isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y] :
    f.appTop.hom.IsIntegral := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  rw [← IsIntegralHom.SpecMap_iff, IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  exact ⟨.of_comp_surjective X.toSpecΓ _, inferInstance⟩

/-- If `X` is an integral scheme that is universally closed over `Spec K`,
then `Γ(X, ⊤)` is a field.
@isnad1 id=isfield.0h3v.s9.efa11ff096ba from=seed src=0 shape=35fd8779 vocab=80e06466
-/
theorem isField_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] : IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/-- If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
then `Γ(X, ⊤)` is a finite field extension over `K`.
@isnad1 id=finite.0h3v.s10.7bfe53f5620d from=seed src=0 shape=3cc0eff7 vocab=0d9356b0
-/
theorem finite_appTop_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] [LocallyOfFiniteType f] :
    f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (isField_of_universallyClosed K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

end GlobalSection

end AlgebraicGeometry
