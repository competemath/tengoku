import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_LevelSubgroup
import Tengoku.FltAnthropic.Definitions.Def_FieldTheory_RatAlgClosureGalois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace groupCohomology

/--
@isnad1 id=isalgclo.0h0v.s4.728a7497b292 from=translated src=- shape=3905abf2 vocab=ff8fdf14
-/
scoped instance isAlgClosure_rat_algebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : G →* (F ≃ₐ[ℚ] F) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r

/--
@isnad1 id=eq.0h5v.s14.7ba16f470e35 from=translated src=- shape=c3850f90 vocab=219814a2
-/
lemma levelRestrict_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) (x : F) :
    (levelRestrict r F g x : AlgebraicClosure ℚ) = r g x :=
  AlgEquiv.restrictNormal_commutes (r g) F x

/--
@isnad1 id=eq.0h3v.s12.9149c669433f from=translated src=- shape=1da5a095 vocab=d24c21a1
-/
lemma ker_levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (levelRestrict r F).ker = F.fixingSubgroup.comap r :=
  (comap_fixingSubgroup_eq_ker r F).symm

def levelQuotientHom (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    G ⧸ F.fixingSubgroup.comap r →* (F ≃ₐ[ℚ] F) :=
  QuotientGroup.lift _ (levelRestrict r F) (by rw [← ker_levelRestrict])

/--
@isnad1 id=eq.0h4v.s14.f4e073b6635a from=translated src=- shape=83a29993 vocab=e8bb12e8
-/
@[simp] lemma levelQuotientHom_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) :
    levelQuotientHom r F (QuotientGroup.mk g) = levelRestrict r F g := rfl

/--
@isnad1 id=injectiv.0h3v.s14.742155ddedba from=translated src=- shape=204e1f45 vocab=a3d2b46c
-/
lemma levelQuotientHom_injective (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    Function.Injective (levelQuotientHom r F) := by
  rw [← MonoidHom.ker_eq_bot_iff, levelQuotientHom, QuotientGroup.ker_lift, ker_levelRestrict, QuotientGroup.map_mk'_self]

def levelQuotientEquiv (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _) ≃* (F ≃ₐ[ℚ] F) :=
  MulEquiv.ofBijective (levelQuotientHom (MonoidHom.id _) F)
    ⟨levelQuotientHom_injective (MonoidHom.id _) F, fun σ => by
      obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) (AlgebraicClosure ℚ) σ
      exact ⟨QuotientGroup.mk g, rfl⟩⟩

/--
@isnad1 id=eq.0h2v.s15.010f6db3e7ba from=translated src=- shape=4fffa32e vocab=ea201e04
-/
@[simp] lemma levelQuotientEquiv_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelQuotientEquiv F (QuotientGroup.mk g) = AlgEquiv.restrictNormalHom F g := rfl

/--
@isnad1 id=eq.0h3v.s15.d6d0540c635f from=translated src=- shape=f11d2c80 vocab=b474f514
-/
lemma levelQuotientEquiv_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F) :
    (levelQuotientEquiv F (QuotientGroup.mk g) x : AlgebraicClosure ℚ) = g x :=
  AlgEquiv.restrictNormal_commutes g F x

end groupCohomology

namespace Rep

open scoped groupCohomology

abbrev ofLevel {k : Type} [CommRing k] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (A : Rep k (F ≃ₐ[ℚ] F)) :
    Rep k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _)) :=
  Rep.res (groupCohomology.levelQuotientEquiv F).toMonoidHom A

end Rep

end
