import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace groupCohomology

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

/--
@isnad1 id=eq.0h3v.s13.a05a9a7822a7 from=translated src=- shape=66c8def9 vocab=3fa00e33
-/
theorem comap_fixingSubgroup_eq_ker (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    F.fixingSubgroup.comap r
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›,
    MonoidHom.comap_ker]
  rfl

/--
@isnad1 id=normal.0h3v.s9.a61fbb8ccb1e from=translated src=- shape=f966c899 vocab=f9287d99
-/
instance normal_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup.comap r).Normal := by
  rw [comap_fixingSubgroup_eq_ker]; exact MonoidHom.normal_ker _

/--
@isnad1 id=finitein.0h3v.s10.5588ecfbfbdd from=translated src=- shape=17d604d2 vocab=c01746f5
-/
instance finiteIndex_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ F] [Normal ℚ F] : (F.fixingSubgroup.comap r).FiniteIndex := by
  rw [comap_fixingSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

/--
@isnad1 id=le.1h4v.s9.fc2ed924d347 from=translated src=- shape=95abc75f vocab=7752f367
-/
theorem comap_fixingSubgroup_antitone {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    F'.fixingSubgroup.comap r ≤ F.fixingSubgroup.comap r :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

end groupCohomology
