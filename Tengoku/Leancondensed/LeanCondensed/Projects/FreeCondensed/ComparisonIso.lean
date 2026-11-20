module

public import Tengoku.Leancondensed.LeanCondensed.Projects.FreeCondensed.LocalSurjectivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- Evaluation on topological free abelian groups is natural in the light profinite source.
@isnad1 id=eq.0h4v.s7.790a61a1cd66 from=translated src=- shape=f1566ce9 vocab=9e917ca4
-/
lemma topologicalFreeEval_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeMap f ≫ topologicalFreeEval T g =
      topologicalFreeEval S (g.comap f.hom.hom) := by
  ext μ
  let L : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeMap f ≫ topologicalFreeEval T g).hom.toLinearMap
  let R : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeEval S (g.comap f.hom.hom)).hom.toLinearMap
  change L μ = R μ
  suffices L = R by rw [this]
  refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
  change (topologicalFreeEval T g).hom ((topologicalFreeMap f).hom (Finsupp.single s (1 : ℤ))) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom (Finsupp.single s (1 : ℤ))
  rw [topologicalFreeMap_single, topologicalFreeEval_single, topologicalFreeEval_single]
  rfl

/-- The induced morphism between represented light condensed abelian groups.-/
noncomputable def topologicalFreeEvalCondensed (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      LightCondensed.topModuleToLightCondAbObj discreteIntTopModule :=
  LightCondensed.topModuleToLightCondAbMap (topologicalFreeEval S f)

/-- The induced morphism from the represented topological free abelian group to the discrete
light condensed abelian group `ℤ`.-/
noncomputable def topologicalFreeEvalDiscrete (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom

/-- Represented topological-free evaluation is natural in the light profinite source.
@isnad1 id=eq.0h4v.s8.e7eaa25b1b0a from=translated src=- shape=2d4df86c vocab=bd93d84f
-/
lemma topologicalFreeEvalCondensed_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g =
      topologicalFreeEvalCondensed S (g.comap f.hom.hom) := by
  ext U h
  change (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g).hom.app U h) =
    (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeEvalCondensed S (g.comap f.hom.hom)).hom.app U h)
  ext u
  change (topologicalFreeEval T g).hom
      ((topologicalFreeMap f).hom
        ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)
  have hn := congrArg (fun m : topologicalFree S ⟶ discreteIntTopModule => m.hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u))
    (topologicalFreeEval_naturality f g)
  simpa using hn

/-- `Z`-valued represented topological-free evaluation is natural in the light profinite source.
@isnad1 id=eq.0h4v.s9.0345c26a16ea from=translated src=- shape=bf8b53cf vocab=55d47141
-/
lemma topologicalFreeEvalDiscrete_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalDiscrete T g =
      topologicalFreeEvalDiscrete S (g.comap f.hom.hom) := by
  simpa [topologicalFreeEvalDiscrete, Category.assoc] using
    congrArg (fun m => m ≫ discreteIntTopModuleCondensedIso.hom)
      (topologicalFreeEvalCondensed_naturality f g)

/-- The represented evaluation induced by `f` sends the Dirac section to `f`.
@isnad1 id=eq.0h2v.s13.e465190d0f04 from=translated src=- shape=0e1b6216 vocab=7978d298
-/
lemma topologicalFreeEvalDiscrete_diracSection (f : LocallyConstant S ℤ) :
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      ((topologicalFreeEvalDiscrete S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))) = f := by
  rw [show topologicalFreeEvalDiscrete S f =
    topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom by rfl]
  change ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      (discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩
        ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
          ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  rw [discreteIntTopModuleCondensedIso_sections]
  change (show LocallyConstant S ℤ from discreteIntTopModuleSectionsEquiv S
      ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  ext s
  dsimp [discreteIntTopModuleSectionsEquiv, discreteIntTopModulePresheafIso,
    topologicalFreeEvalCondensed]
  change (topologicalFreeEval S f).hom
      ((show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) s) = f s
  rw [topologicalFreeDiracSection_yoneda_apply]
  exact topologicalFreeEval_single S f s

/-- The sheaf-level morphism induced by the presheaf comparison from formal free sections to
represented topological-free sections.-/
noncomputable def freePresheafComparisonSheafification :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S where
  hom := CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

/--
@isnad1 id=eq.0h1v.s9.a0254f228bbd from=translated src=- shape=fa35e67e vocab=d951b806
-/
@[reassoc (attr := simp)]
lemma toSheafify_freePresheafComparisonSheafification :
    CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom =
    freePresheafToTopologicalFreePresheaf S := by
  exact CategoryTheory.toSheafify_sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

/-- At the represented identity section, the free/sheaf adjunction unit is the sheafification of
the presheaf free generator.
@isnad1 id=eq.0h1v.s12.659f1f1568b1 from=translated src=- shape=6241ff79 vocab=74214d37
-/
lemma freeForgetAdjunction_unit_app_id :
    ((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S) =
      (CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S)) := by
  rw [LightCondensed.freeForgetAdjunction, CategoryTheory.Sheaf.adjunction_unit_app_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified presheaf comparison sends the represented Dirac generator to the represented
topological Dirac section.
@isnad1 id=eq.0h1v.s13.6e77f045c6d4 from=translated src=- shape=9645a38d vocab=202384b9
-/
lemma freePresheafComparison_diracSection :
    (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S) := by
  have h := congrArg (fun η : freePresheaf S ⟶ topologicalFreePresheaf S =>
      η.app ⟨S⟩ (ModuleCat.freeMk (𝟙 S)))
    (toSheafify_freePresheafComparisonSheafification S)
  change ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  exact h.trans (by
    change (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (freePresheafToTopologicalFreePresheaf S).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
      (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))
    rw [freePresheafToTopologicalFreePresheaf_app_freeMk]
    ext s
    rw [topologicalFreeDiracSection_yoneda_apply]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Under the free/forget adjunction, the sheafified presheaf comparison is characterized by the
represented topological Dirac section.
@isnad1 id=eq.0h1v.s11.4fa177af70e8 from=translated src=- shape=24d7768b vocab=18316c90
-/
lemma freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freePresheafComparisonSheafification S) = topologicalFreeDiracSection S := by
  apply (coherentTopology LightProfinite).yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  change (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      (((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S)) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  rw [freeForgetAdjunction_unit_app_id]
  exact freePresheafComparison_diracSection S

/-- The canonical comparison from the free light condensed abelian group to the light condensed
abelian group represented by the free topological abelian group.-/
noncomputable def freeToTopologicalFree :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)).symm
    (topologicalFreeDiracSection S)

/--
@isnad1 id=eq.0h1v.s11.3cb3cda3edc7 from=translated src=- shape=24d7768b vocab=a95d250b
-/
@[simp]
lemma freeForgetAdjunction_homEquiv_freeToTopologicalFree :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freeToTopologicalFree S) = topologicalFreeDiracSection S := by
  simp [freeToTopologicalFree]

/-- The existing `freeToTopologicalFree` morphism is the sheaf-level morphism induced by the
presheaf comparison.
@isnad1 id=eq.0h1v.s8.d7dd74cfbaa6 from=translated src=- shape=44a8abe3 vocab=38f93bfe
-/
lemma freeToTopologicalFree_eq_sheafified_presheaf_comparison :
    freeToTopologicalFree S = freePresheafComparisonSheafification S := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed S)).injective
  rw [freeForgetAdjunction_homEquiv_freeToTopologicalFree,
    freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification]

/-- The comparison from the free light condensed abelian group to the represented topological free
abelian group is natural in the light profinite source.
@isnad1 id=eq.0h3v.s10.dc386c50548b from=translated src=- shape=45054e37 vocab=194c5f6d
-/
lemma freeToTopologicalFree_naturality {S T : LightProfinite.{0}} (f : S ⟶ T) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ freeToTopologicalFree T =
      freeToTopologicalFree S ≫ topologicalFreeCondensedMap f := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed T)).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeToTopologicalFree]
  simp
  exact topologicalFreeDiracSection_naturality f

/-- The represented topological-free sheaf is isomorphic to its sheafification.-/
noncomputable def topologicalFreeCondensedSheafifyIso (S : LightProfinite.{0}) :
    topologicalFreeCondensed S ≅
      (CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).obj
        (topologicalFreePresheaf S) where
  hom := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).hom)
  inv := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).inv)
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).inv_hom_id

/-- The sheafified presheaf comparison is the comparison followed by the inverse sheafification
identification of the represented target.
@isnad1 id=eq.0h1v.s10.fd20158520b1 from=translated src=- shape=c3614494 vocab=5e10cd3b
-/
lemma sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv
    (S : LightProfinite.{0}) :
    (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S)) ≫
        (topologicalFreeCondensedSheafifyIso S).inv) =
      freePresheafComparisonSheafification S := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [topologicalFreeCondensedSheafifyIso]
  rw [CategoryTheory.isoSheafify_inv]
  change CategoryTheory.sheafifyMap (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) ≫
        CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
          (𝟙 (topologicalFreePresheaf S)) (topologicalFreeCondensed S).property =
      CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
        (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property
  erw [CategoryTheory.sheafifyMap_sheafifyLift]
  simp

/--
@isnad1 id=isiso.0h1v.s9.f4d625dca3b8 from=translated src=- shape=f6b606a1 vocab=26b314ff
-/
instance instIsIso_sheafifiedPresheafComparison (S : LightProfinite.{0}) :
    IsIso (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S))) := by
  rw [← CategoryTheory.GrothendieckTopology.W_iff]
  exact (coherentTopology LightProfinite).W_of_isLocallyBijective
    (freePresheafToTopologicalFreePresheaf S)

/--
@isnad1 id=isiso.0h1v.s8.94c2e12b3af3 from=translated src=- shape=6215046a vocab=cab7ef21
-/
instance instIsIso_freeToTopologicalFree (S : LightProfinite.{0}) :
    IsIso (freeToTopologicalFree S) := by
  rw [freeToTopologicalFree_eq_sheafified_presheaf_comparison]
  rw [← sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv]
  exact IsIso.comp_isIso' (instIsIso_sheafifiedPresheafComparison S) (Iso.isIso_inv _)

noncomputable def freeTopologicalFreeIso (S : LightProfinite.{0}) :
    (free ℤ).obj S.toCondensed ≅ topologicalFreeCondensed S :=
  asIso (freeToTopologicalFree S)

/--
@isnad1 id=eq.0h1v.s9.1f5c32df055f from=translated src=- shape=3ce754f3 vocab=a4c12f38
-/
lemma freeTopologicalFreeIso_hom (S : LightProfinite.{0}) :
    (freeTopologicalFreeIso S).hom = freeToTopologicalFree S := by
  rfl

/-- Applying the comparison to a section transported back along `freeTopologicalFreeIso.symm`
recovers the original represented topological-free section.
@isnad1 id=eq.0h3v.s12.4b39b6434272 from=translated src=- shape=8385ca9d vocab=fb7bdb14
-/
@[simp]
lemma freeToTopologicalFree_app_section_of_iso_symm
    (T X : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩) :
    (freeToTopologicalFree T).hom.app ⟨X⟩
      ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s) = s := by
  change ((freeTopologicalFreeIso T).hom.hom.app ⟨X⟩)
      ((freeTopologicalFreeIso T).inv.hom.app ⟨X⟩ s) = s
  change ((freeTopologicalFreeIso T).inv ≫ (freeTopologicalFreeIso T).hom).hom.app ⟨X⟩ s = s
  simp

/-- Restrictions of a free section pulled back from the represented topological-free sheaf are
identified by applying the free/topological-free comparison.
@isnad1 id=eq.0h5v.s13.15ecc8a653cb from=translated src=- shape=6d57e273 vocab=01564baa
-/
@[simp]
lemma freeToTopologicalFree_app_map_section_of_iso_symm
    (T X Y : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩)
    (f : Y ⟶ X) :
    (freeToTopologicalFree T).hom.app ⟨Y⟩
      (((free ℤ).obj T.toCondensed).obj.map f.op
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) =
      (topologicalFreeCondensed T).obj.map f.op s := by
  have hX := freeToTopologicalFree_app_section_of_iso_symm T X s
  have hn := ConcreteCategory.congr_hom ((freeToTopologicalFree T).hom.naturality f.op)
    ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)
  change (freeToTopologicalFree T).hom.app ⟨Y⟩
      (((free ℤ).obj T.toCondensed).obj.map f.op
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) =
    (topologicalFreeCondensed T).obj.map f.op
      ((freeToTopologicalFree T).hom.app ⟨X⟩
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) at hn
  rw [hX] at hn
  exact hn

/-- The free/topological-free comparison is injective on sections over every light profinite.
@isnad1 id=injectiv.0h2v.s11.3d7de86a17d2 from=translated src=- shape=38abb2f4 vocab=57a9ec77
-/
lemma freeToTopologicalFree_app_injective
    (T X : LightProfinite.{0}) :
    Function.Injective ((freeToTopologicalFree T).hom.app ⟨X⟩) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

/-- A free section is determined by its image in the represented topological-free sheaf.
@isnad1 id=eq.1h4v.s12.9e02db75a4e6 from=translated src=- shape=44dedc55 vocab=03d588c8
-/
lemma freeSection_eq_of_freeToTopologicalFree_eq
    (T X : LightProfinite.{0})
    {u v : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩}
    (h : (freeToTopologicalFree T).hom.app ⟨X⟩ u =
      (freeToTopologicalFree T).hom.app ⟨X⟩ v) :
    u = v :=
  freeToTopologicalFree_app_injective T X h

/-- Convenience form for comparing free sections by comparing the resulting measures pointwise
after applying the free/topological-free comparison.
@isnad1 id=eq.1h4v.s12.755eaa5867d1 from=translated src=- shape=e0c920d3 vocab=87ac4a4d
-/
lemma freeSection_map_eq_of_pointwise_measure_eq
    (T X : LightProfinite.{0})
    {u v : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩}
    (h : ∀ x : X,
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
        (freeToTopologicalFree T).hom.app ⟨X⟩ u) x =
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
        (freeToTopologicalFree T).hom.app ⟨X⟩ v) x) :
    u = v := by
  apply freeSection_eq_of_freeToTopologicalFree_eq T X
  apply ContinuousMap.ext
  intro x
  exact h x

abbrev freeLightProfiniteMap : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ⟶
    sequentialToLightCondSet.obj (lightCondSetToSequential.obj
      ((forget ℤ).obj ((free ℤ).obj S.toCondensed))) :=
  LightCondSet.sequentialAdjunction.unit.app <| (forget ℤ).obj <| (free ℤ).obj S.toCondensed

namespace FreeImage

open LightProfinite.FreeImage

end FreeImage

/-- The sequential finite-measure model for the free light condensed abelian group on `S`.-/
abbrev freeMeasureSequential : Sequential :=
  LightProfinite.FreeImage.sequential S

end LightCondAb
