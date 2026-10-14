/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Tengoku

/-!
# Closed immersions

This module packages the `TopCat` API for the closed inclusion `closedIncl : TopCat.of s ⟶ X`
and the stalk comparisons needed in the closed-immersion step of Grothendieck vanishing.

Main results:
- `closedIncl_isClosedEmbedding` and `closedIncl_isInducing` record the basic topology of
  the closed inclusion.
- `closedIncl_map_eq_bot_of_le_compl` shows that opens contained in the complement pull back
  to `⊥` on the closed subspace.
- `pushforward_closedIncl_stalk_eq_zero` identifies stalks of a closed-immersion
  pushforward away from the closed subset with zero.
- `closedIncl_pushforward_preservesEpis/Monos` and
  `closedIncl_pushforward_shortExact` package exactness of pushforward along the
  closed inclusion for `AddCommGrpCat`-valued sheaves.
- `stalkFunctor_map_iso_toSheafify` identifies the stalk of sheafification with an isomorphism.
- `closedIncl_counit_isIso` identifies the pushforward-pullback counit for
  presheaves on the closed subspace carrying a sheaf condition.
- `stalkPullbackHom_naturality` is the stalk-level naturality needed to compare the unit with
  the counit isomorphism.
- `closedIncl_unit_stalk_isIso` shows that the adjunction unit is an isomorphism on stalks at
  points of the closed subset.
- `epi_unit_of_closedImmersion` upgrades the adjunction unit to an epi of sheaves.
- `closedImmersionSES` and `closedImmersionSES_shortExact` package the short exact sequence
  `0 → ker(η) → F → i_*(i^*F) → 0` associated to a closed immersion.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

instance sheafAbelianAddCommGrp (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

namespace TopCat

/-- Closed inclusion `s ↪ X` as a morphism in `TopCat`. -/
def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

/--
@isnad1 id=eq.1h2v.s7.d81abc62193e from=translated src=- shape=a3b11142 vocab=9001eb43
-/
lemma set_range_closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Set.range (closedIncl hs : s → X) = s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/--
@isnad1 id=isclosed.1h2v.s7.1081049d9aa3 from=translated src=- shape=f618181a vocab=15962465
-/
lemma closedIncl_isClosedEmbedding {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsClosedEmbedding (closedIncl hs) :=
  hs.isClosedEmbedding_subtypeVal

/--
@isnad1 id=isinduci.1h2v.s7.6dcc820b13d5 from=translated src=- shape=f618181a vocab=40505091
-/
lemma closedIncl_isInducing {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsInducing (closedIncl hs) :=
  (closedIncl_isClosedEmbedding hs).isInducing

/--
@isnad1 id=eq.2h3v.s9.3d31763ee401 from=translated src=- shape=c901456f vocab=eb255f8e
-/
theorem closedIncl_map_eq_bot_of_le_compl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {U : Opens X} (hU : U ≤ ⟨sᶜ, hs.isOpen_compl⟩) :
    (Opens.map (closedIncl hs)).obj U = ⊥ := by
  apply Opens.ext
  change (closedIncl hs : s → X) ⁻¹' (U : Set X) = (⊥ : Opens (TopCat.of s))
  have hdisj : Disjoint (U : Set X) (Set.range (closedIncl hs : s → X)) := by
    rw [set_range_closedIncl hs]
    exact Set.disjoint_left.mpr fun x hxU hxS ↦ hU hxU hxS
  simpa using (Set.preimage_eq_empty hdisj)

/--
@isnad1 id=isiso.1h5v.s8.3b3c0f6f7f04 from=translated src=- shape=b2b7cb46 vocab=09e7e5e2
-/
instance closedIncl_stalkPushforward_isIso {X : TopCat.{u}} {s : Set X} {hs : IsClosed s}
    {C : Type*} [Category.{u} C] [HasColimits C]
    {F : (TopCat.of s).Presheaf C} {x : TopCat.of s} :
    IsIso (Presheaf.stalkPushforward C (closedIncl hs) F x) :=
  Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    C (closedIncl_isInducing hs) F x

/--
@isnad1 id=isbasis.1h3v.s7.e97e2f208986 from=translated src=- shape=39e506c3 vocab=596d5597
-/
lemma opensMap_range_isBasis_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    Opens.IsBasis (Set.range (Opens.map f).obj) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  refine ⟨U, ?_, hx, le_rfl⟩
  refine ⟨hf.functorObj U, ?_⟩
  simpa using hf.map_functorObj U

/--
@isnad1 id=iscoverd.1h3v.s7.4ec294081961 from=translated src=- shape=cc79c6c0 vocab=dd3ca5c7
-/
lemma opensMap_isCoverDense_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    (Opens.map f).IsCoverDense (Opens.grothendieckTopology X) := by
  rw [TopCat.Opens.coverDense_iff_isBasis]
  exact opensMap_range_isBasis_of_isInducing hf

/--
@isnad1 id=islocall.0h3v.s6.2134074ab7f9 from=translated src=- shape=1bc4c305 vocab=7fbadd8b
-/
instance opensMap_isLocallyFull {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (Opens.map f).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V i
    rw [Opens.grothendieckTopology]
    intro x hx
    refine ⟨(Opens.map f).obj (U ⊓ V), (Opens.map f).map (Opens.infLELeft U V), ?_, ?_⟩
    · refine ⟨U ⊓ V, Opens.infLELeft U V, 𝟙 _, ?_, by simp⟩
      refine ⟨Opens.infLERight U V, ?_⟩
      exact Subsingleton.elim _ _
    · exact ⟨hx, i.le hx⟩

/--
@isnad1 id=injectiv.0h8v.s8.e988a8d397af from=translated src=- shape=7916f107 vocab=55bb8df8
-/
theorem locallyInjective_stalkFunctor_map_injective
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    {X : TopCat.{u}} {F G : X.Presheaf C} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
  ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor C x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.exists_germ_eq s
  obtain ⟨V, hxV, sV, hsV⟩ := F.exists_germ_eq t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hnat (Y : Opens X) (iWY : W ⟶ Y) (sY : CC (F.obj (op Y))) :
      T.app (op W) (F.map iWY.op sY) = G.map iWY.op (T.app (op Y) sY) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEq' : T.app (op W) (F.map iWU.op sU) =
      T.app (op W) (F.map iWV.op sV) := by rw [hnat _ iWU, hnat _ iWV]; exact hEq
  have hloc := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X) (φ := T)
    (x := F.map iWU.op sU) (y := F.map iWV.op sV) hEq'
  rw [Opens.grothendieckTopology] at hloc
  rcases hloc x hxW with ⟨Z, iZW, hEqZ, hxZ⟩
  apply F.germ_ext Z hxZ (iZW ≫ iWU) (iZW ≫ iWV)
  simpa using hEqZ

/--
@isnad1 id=isiso.0h6v.s8.55c6c9ea312b from=translated src=- shape=fdba9561 vocab=86ef1e3c
-/
theorem stalkFunctor_map_iso_toSheafify
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology X) C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    (P : X.Presheaf C) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact locallyInjective_stalkFunctor_map_injective
      (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) x
  · have hls : TopCat.Presheaf.IsLocallySurjective
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
        dsimp [TopCat.Presheaf.IsLocallySurjective]; infer_instance
    exact
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)).mp hls) x

/--
@isnad1 id=isiso.1h6v.s10.021db1dc8b5b from=translated src=- shape=1be9273e vocab=3dee912b
-/
theorem closedIncl_counit_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf C (TopCat.of s)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app
      F) := by
  let : (Opens.map (closedIncl hs)).IsCoverDense
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isCoverDense_of_isInducing (closedIncl_isInducing hs)
  let : (Opens.map (closedIncl hs)).IsLocallyFull
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isLocallyFull (closedIncl hs)
  let : (Opens.map (closedIncl hs)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s)) :=
    CategoryTheory.Functor.IsCoverDense.isContinuous
      (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology (TopCat.of s))
      (G := Opens.map (closedIncl hs))
      (coverPreserving_opens_map (closedIncl hs))
  have : (TopCat.Sheaf.pushforward C (closedIncl hs)).Full := by
    change ((Opens.map (closedIncl hs)).sheafPushforwardContinuous C
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s))).Full
    infer_instance
  have : (TopCat.Sheaf.pushforward C (closedIncl hs)).Faithful := by
    change ((Opens.map (closedIncl hs)).sheafPushforwardContinuous C
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s))).Faithful
    infer_instance
  infer_instance

end TopCat

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
    if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero.
@isnad1 id=eq.3h5v.s10.c99cf0d4bb37 from=translated src=- shape=bb6ab71f vocab=c78d059f
-/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)} (hG : G.IsSheaf)
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G)) :
    a = 0 := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s) := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G
  obtain ⟨U, hxU, sU, rfl⟩ := F'.exists_germ_eq a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_map : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    TopCat.closedIncl_map_eq_bot_of_le_compl (hs := hs) (U := W) inf_le_right
  have : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_map]
    exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  rw [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]
  exact map_zero _

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    presheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient
    space whenever `f` is locally surjective.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside).
@isnad1 id=epi.4h5v.s13.353f7878e1eb from=translated src=- shape=00b3d362 vocab=913d00fa
-/
theorem epi_pushforward_map_closedIncl_of_locallySurjective
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf_loc : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
            ObjectProperty.homMk f)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) := ObjectProperty.homMk f
  let : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    have hEpiF : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f)).mp hf_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      erw [← Category.assoc]
      rw [TopCat.Presheaf.stalkFunctor_map_germ U ((TopCat.closedIncl hs) z) hU
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f)]
      erw [Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f))
    have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) F z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) G z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    have hcomp : Epi (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) F z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z)
        (inferInstance : Epi (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
          (TopCat.closedIncl hs) F z))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f)
        hEpiF
    have hcomp' : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z) := by
      rw [hnat]; exact hcomp
    exact (epi_comp_iff_of_isIso _
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z)).mp hcomp'
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

namespace TopCat

-- Stalk pullback hom naturality

end TopCat

-- The adjunction unit `F → i_*(i^*F)` is epi for closed immersions.

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let closedIncl := TopCat.closedIncl hZ
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)
