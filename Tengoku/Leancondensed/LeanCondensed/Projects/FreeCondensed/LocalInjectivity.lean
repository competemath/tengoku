module

public import Tengoku.Leancondensed.LeanCondensed.Projects.FreeCondensed.TopologicalFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- A single effective epimorphism lying in an equalizer sieve gives a coherent covering of that
sieve.  This is the site-theoretic target for the finite closed-cover part of local injectivity.
@isnad1 id=mem.1h6v.s10.6a3a2f63bb50 from=translated src=- shape=45b68bce vocab=36eef9e9
-/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpi
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U V : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (π : V ⟶ U) [EffectiveEpi π]
    (hπ : F.map π.op x = F.map π.op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  refine ⟨Unit, inferInstance, (fun _ => V), (fun _ => π), ?_, ?_⟩
  · simpa [CategoryTheory.effectiveEpi_iff_effectiveEpiFamily] using (inferInstance : EffectiveEpi π)
  · intro _
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ

/-- A closed subset of a light profinite space, with the induced topology, is light profinite.-/
noncomputable def closedSubLightProfinite {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    LightProfinite.{0} :=
  @LightProfinite.of s inferInstance (isCompact_iff_compactSpace.mp hs.isCompact)
    inferInstance inferInstance inferInstance

/-- The inclusion of a closed light-profinite subspace.-/
noncomputable def closedSubLightProfiniteι {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    closedSubLightProfinite s hs ⟶ X := by
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  exact CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

/--
@isnad1 id=eq.1h3v.s9.88d7f52a9d61 from=translated src=- shape=b66831ce vocab=3cd540f4
-/
@[simp]
lemma closedSubLightProfiniteι_apply {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s)
    (x : closedSubLightProfinite s hs) : closedSubLightProfiniteι s hs x = (x : s).1 := rfl

/-- A finite jointly-surjective family in `LightProfinite` is an effective-epi family.
@isnad1 id=effectiv.1h4v.s9.c3e33a25cd82 from=translated src=- shape=8fc12964 vocab=9267fc7f
-/
lemma effectiveEpiFamily_of_jointly_surjective {α : Type} [Finite α]
    {B : LightProfinite.{0}} (X : α → LightProfinite.{0}) (π : (a : α) → X a ⟶ B)
    (hπ : ∀ b : B, ∃ a, ∃ x : X a, π a x = b) : EffectiveEpiFamily X π := by
  rw [← CategoryTheory.effectiveEpi_desc_iff_effectiveEpiFamily]
  rw [LightProfinite.effectiveEpi_iff_surjective]
  intro b
  obtain ⟨a, x, hx⟩ := hπ b
  refine ⟨Sigma.ι X a x, ?_⟩
  exact (ConcreteCategory.congr_hom (Sigma.ι_desc π a) x).trans hx

/-- A finite effective-epi family lying in an equalizer sieve gives a coherent covering of that
sieve.
@isnad1 id=mem.1h7v.s10.f87a9c1a8d3c from=translated src=- shape=176a1b3b vocab=5992d73f
-/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (V : α → LightProfinite.{0}) (π : (a : α) → V a ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ a, F.map (π a).op x = F.map (π a).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun a => by
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ a⟩

/-- A finite effective-epi family with local preimages gives a coherent covering of the image
sieve.
@isnad1 id=mem.1h8v.s10.7116a5d157f7 from=translated src=- shape=04ef7a0e vocab=da57e825
-/
lemma presheaf_imageSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun i => by
    simpa [CategoryTheory.Presheaf.imageSieve] using hπ i⟩

/-- A finite jointly-surjective family with local preimages gives a coherent covering of the image
sieve.
@isnad1 id=mem.2h8v.s11.38d3a9e96909 from=translated src=- shape=38d983ad vocab=0ee9eb06
-/
lemma presheaf_imageSieve_mem_of_finite_jointly_surjective
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    (hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u)
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact presheaf_imageSieve_mem_of_effectiveEpiFamily φ s V π hπ

/-- A finite closed cover whose inclusions lie in an equalizer sieve gives a coherent covering of
that sieve.  This packages the closed-cover replacement for the tempting but invalid clopen
refinement.
@isnad1 id=mem.3h6v.s10.ccfd50b3295e from=translated src=- shape=6aa9f2f8 vocab=5ee5491c
-/
lemma freePresheaf_equalizerSieve_mem_of_finite_closed_cover
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (C : α → Set U) (hC : ∀ a, IsClosed (C a))
    (hcover : ∀ u : U, ∃ a, u ∈ C a)
    (hπ : ∀ a, F.map (closedSubLightProfiniteι (C a) (hC a)).op x =
      F.map (closedSubLightProfiniteι (C a) (hC a)).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun a => closedSubLightProfinite (C a) (hC a)
  let π : (a : α) → V a ⟶ U := fun a => closedSubLightProfiniteι (C a) (hC a)
  have hsurj : ∀ u : U, ∃ a, ∃ x : V a, π a x = u := by
    intro u
    obtain ⟨a, hu⟩ := hcover u
    refine ⟨a, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C a) (hC a) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily x y V π hπ

/-- Pulling back a presheaf equalizer sieve restricts the two sections along the same arrow.
@isnad1 id=eq.0h6v.s10.ee7051529195 from=translated src=- shape=d80e6e5e vocab=b885801a
-/
lemma _root_.CategoryTheory.Presheaf.equalizerSieve_pullback_eq
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U V : LightProfinite.{0}} (π : V ⟶ U)
    (x y : F.obj ⟨U⟩) :
    (CategoryTheory.Presheaf.equalizerSieve x y).pullback π =
      CategoryTheory.Presheaf.equalizerSieve (F.map π.op x) (F.map π.op y) := by
  ext W f
  simp [CategoryTheory.Presheaf.equalizerSieve]

/-- If the equalizer sieve is covering locally on every member of a finite closed cover, then it is
covering on the original space.  This is the transitivity form of the closed-cover reduction.
@isnad1 id=mem.3h6v.s11.868189123fcb from=translated src=- shape=b65583e2 vocab=5ee5491c
-/
lemma presheaf_equalizerSieve_mem_of_finite_closed_cover_locally
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩)
    (C : α → Set U) (hC : ∀ i, IsClosed (C i))
    (hcover : ∀ u : U, ∃ i, u ∈ C i)
    (hlocal : ∀ i,
      CategoryTheory.Presheaf.equalizerSieve
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op x)
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op y) ∈
          (coherentTopology LightProfinite)
            (closedSubLightProfinite (C i) (hC i))) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈
      (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun i => closedSubLightProfinite (C i) (hC i)
  let π : (i : α) → V i ⟶ U := fun i => closedSubLightProfiniteι (C i) (hC i)
  have hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u := by
    intro u
    obtain ⟨i, hu⟩ := hcover u
    refine ⟨i, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C i) (hC i) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  let S₀ : Sieve U := Sieve.ofArrows V π
  have hS₀ : S₀ ∈ (coherentTopology LightProfinite) U := by
    apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    exact ⟨α, inferInstance, V, π, inferInstance, fun i => Sieve.ofArrows_mk V π i⟩
  refine (coherentTopology LightProfinite).transitive hS₀
    (CategoryTheory.Presheaf.equalizerSieve x y) ?_
  intro Y f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff V π f).mp hf
  have hπ : (CategoryTheory.Presheaf.equalizerSieve x y).pullback (π i) ∈
      (coherentTopology LightProfinite) (V i) := by
    simpa [S₀, V, π, CategoryTheory.Presheaf.equalizerSieve_pullback_eq] using hlocal i
  simpa [Sieve.pullback_comp] using
    ((coherentTopology LightProfinite).pullback_stable g hπ)

/-- Equality-pattern loci cut out by finitely many equalities between maps to a light profinite
space are closed.  The second TFC3 round uses these as closed members of a coherent cover; the
remaining coefficient extraction happens after restricting the free presheaf to these loci.
@isnad1 id=isclosed.0h5v.s10.a746c49f3b1e from=translated src=- shape=c1819919 vocab=af008cea
-/
lemma finiteMapEqualityPattern_isClosed {α : Type} [Finite α] {U S : LightProfinite.{0}}
    (f : α → (U ⟶ S)) (r : α → α → Prop) :
    IsClosed {u : U | ∀ i j, r i j → (f i) u = (f j) u} := by
  classical
  rw [show {u : U | ∀ i j, r i j → (f i) u = (f j) u} =
      ⋂ i, ⋂ j, ⋂ _h : r i j, {u : U | (f i) u = (f j) u} by
    ext u
    simp]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (f i).hom.hom.continuous (f j).hom.hom.continuous

/-- If `f` is injective on the union of the supports of two finitely supported functions, equality
after `Finsupp.mapDomain f` reflects equality.
@isnad1 id=eq.2h5v.s6.a712117e3469 from=translated src=- shape=dc95f178 vocab=c64f68c1
-/
lemma finsupp_mapDomain_eq_of_eq_of_injOn_support_union {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) {a b : α →₀ ℤ}
    (hinj : Set.InjOn f ((↑((a.support : Finset α) ∪ b.support) : Set α)))
    (h : Finsupp.mapDomain f a = Finsupp.mapDomain f b) : a = b := by
  ext x
  by_cases hx : x ∈ (a.support : Finset α) ∪ b.support
  · have ha : (Finsupp.mapDomain f a) (f x) = a x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_left _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : a x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    have hb : (Finsupp.mapDomain f b) (f x) = b x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_right _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : b x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    exact ha ▸ hb ▸ DFunLike.congr_fun h (f x)
  · have hxa : x ∉ a.support := fun hxa => hx (Finset.mem_union_left _ hxa)
    have hxb : x ∉ b.support := fun hxb => hx (Finset.mem_union_right _ hxb)
    have hax : a x = 0 := by
      by_contra hne
      exact hxa ((Finsupp.mem_support_iff).mpr hne)
    have hbx : b x = 0 := by
      by_contra hne
      exact hxb ((Finsupp.mem_support_iff).mpr hne)
    simp [hax, hbx]

/-- If a finitely supported integer combination vanishes after `mapDomain`, then every support
point collides under the domain map with another support point.
@isnad1 id=ex.2h5v.s7.11ceb6e2733e from=translated src=- shape=967c80e9 vocab=69f95b7b
-/
lemma finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (c : α →₀ ℤ) {x : α} (hx : x ∈ c.support)
    (f : α → β) (hzero : Finsupp.mapDomain f c = 0) :
    ∃ y, y ∈ c.support ∧ y ≠ x ∧ f y = f x := by
  by_contra hnone
  have hsum : (Finsupp.mapDomain f c) (f x) = c x := by
    rw [Finsupp.mapDomain_apply_eq_sum]
    refine Finset.sum_eq_single x ?_ ?_
    · intro y hy hyx
      rw [Finset.mem_filter] at hy
      exact (hnone ⟨y, hy.1, hyx, hy.2⟩).elim
    · intro hxnot
      exact (hxnot (by
        rw [Finset.mem_filter]
        exact ⟨hx, rfl⟩)).elim
  have hzero_apply : (Finsupp.mapDomain f c) (f x) = 0 := by
    rw [hzero]
    rfl
  rw [hsum] at hzero_apply
  exact (Finsupp.mem_support_iff.mp hx) hzero_apply

/-- If two distinct support points collide under the domain map, then the support of the
`mapDomain` result has strictly smaller cardinality.  This only uses the upper bound by the image
of the original support, so cancellations after `mapDomain` are allowed.
@isnad1 id=lt.4h6v.s6.70c2e7218cad from=translated src=- shape=220395fe vocab=f7883b97
-/
lemma finsupp_mapDomain_support_card_lt_of_pair_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (c : α →₀ ℤ)
    {x y : α} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hne : x ≠ y) (hxy : f x = f y) :
    (Finsupp.mapDomain f c).support.card < c.support.card := by
  have hsubset : (Finsupp.mapDomain f c).support ⊆ c.support.image f := by
    exact Finsupp.mapDomain_support
  have hcard_support : (Finsupp.mapDomain f c).support.card ≤ (c.support.image f).card :=
    Finset.card_le_card hsubset
  have hnotinj : ¬ Set.InjOn f (c.support : Set α) := by
    intro hinj
    exact hne (hinj (by exact Finset.mem_coe.mpr hx) (by exact Finset.mem_coe.mpr hy) hxy)
  have hcard_image_lt : (c.support.image f).card < c.support.card := by
    have hle : (c.support.image f).card ≤ c.support.card := Finset.card_image_le
    have hnecard : (c.support.image f).card ≠ c.support.card := by
      intro heq
      exact hnotinj ((Finset.card_image_iff (s := c.support) (f := f)).mp heq)
    exact Nat.lt_of_le_of_ne hle hnecard
  exact lt_of_le_of_lt hcard_support hcard_image_lt

/--
@isnad1 id=eq.0h6v.s11.ee22d71b5580 from=translated src=- shape=466ec7d8 vocab=0df6d724
-/
lemma freePresheaf_map_sub
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (a b : (freePresheaf S).obj ⟨U⟩) :
    (freePresheaf S).map π.op (a - b) =
      (freePresheaf S).map π.op a - (freePresheaf S).map π.op b := by
  exact ((freePresheaf S).map π.op).hom.map_sub a b

/--
@isnad1 id=lt.4h7v.s11.cfa69561eac8 from=translated src=- shape=f65f73bf vocab=27b37826
-/
lemma freePresheaf_restrict_support_card_lt_of_eq_on_pair
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (c : (freePresheaf S).obj ⟨U⟩)
    {g h : U ⟶ S} (hg : g ∈ c.support) (hh : h ∈ c.support)
    (hne : g ≠ h) (heq : π ≫ g = π ≫ h) :
    (((freePresheaf S).map π.op c).support.card < c.support.card) := by
  classical
  change (Finsupp.mapDomain (fun g : U ⟶ S => π ≫ g) c).support.card < c.support.card
  exact finsupp_mapDomain_support_card_lt_of_pair_eq (fun g : U ⟶ S => π ≫ g) c hg hh hne heq

/--
@isnad1 id=eq.1h5v.s11.ec4ffb646551 from=translated src=- shape=925802f0 vocab=1638d208
-/
lemma freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero
    (S U : LightProfinite.{0}) {a b : (freePresheaf S).obj ⟨U⟩}
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b)
    (u : U) :
    Finsupp.mapDomain (fun g : U ⟶ S => g u) (a - b) = 0 := by
  classical
  let f : S.toCondensed.obj.obj ⟨U⟩ → S :=
    fun g => ((show U ⟶ S from g) u)
  change Finsupp.mapDomain f (a - b) = 0
  have hpoint : Finsupp.mapDomain f a = Finsupp.mapDomain f b := by
    simpa [f] using freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq S U h u
  calc
    Finsupp.mapDomain f (a - b) = Finsupp.mapDomain f a - Finsupp.mapDomain f b := by
      exact Finsupp.mapDomain_sub
    _ = 0 := by simp [hpoint]

/-- Indices for the one-step collision cover: support maps distinct from the chosen `g₀`.-/
def freePresheaf_collisionCoverIndex
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) : Type :=
  {g : S.toCondensed.obj.obj ⟨U⟩ // g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}

/--
@isnad1 id=finite.0h4v.s6.0b9e91e10a03 from=translated src=- shape=9fc5412e vocab=213f0077
-/
instance freePresheaf_collisionCoverIndex_finite
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    Finite (freePresheaf_collisionCoverIndex S U c g₀) := by
  classical
  let collisionSet : Set (S.toCondensed.obj.obj ⟨U⟩) :=
    {g | g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}
  have hfinite : collisionSet.Finite := by
    refine Set.Finite.ofFinset
      (c.support.filter fun g => (show U ⟶ S from g) ≠ g₀) ?_
    intro g
    simp [collisionSet]
  change Finite collisionSet
  exact hfinite.to_subtype

/-- The closed equality locus for a collision-cover index.-/
noncomputable def freePresheaf_collisionCoverSet
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    freePresheaf_collisionCoverIndex S U c g₀ → Set U :=
  fun g => {u | (show U ⟶ S from g.1) u = g₀ u}

/--
@isnad1 id=isclosed.0h5v.s6.779ab133bc45 from=translated src=- shape=c04409f9 vocab=12bb693b
-/
lemma freePresheaf_collisionCover_isClosed
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    ∀ i, IsClosed (freePresheaf_collisionCoverSet S U c g₀ i) := by
  intro i
  exact isClosed_eq (show U ⟶ S from i.1).hom.hom.continuous g₀.hom.hom.continuous

/--
@isnad1 id=ex.2h5v.s10.b99d90cd4f07 from=translated src=- shape=3dcc1955 vocab=c92784a2
-/
lemma freePresheaf_collisionCover_covers_of_pointwise_zero
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (hzero : ∀ u : U,
      Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0) :
    ∀ u : U, ∃ i, u ∈ freePresheaf_collisionCoverSet S U c g₀ i := by
  classical
  intro u
  obtain ⟨g, hg, hne, heq⟩ :=
    finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero c hg₀
      (fun g : U ⟶ S => g u) (hzero u)
  exact ⟨⟨g, hg, hne⟩, heq⟩

/--
@isnad1 id=other.1h5v.s10.3496f4307c6b from=translated src=- shape=43579b5c vocab=a5057e09
-/
lemma freePresheaf_collisionCover_restrict_card_lt
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (i : freePresheaf_collisionCoverIndex S U c g₀) :
    let C := freePresheaf_collisionCoverSet S U c g₀ i
    let hC := freePresheaf_collisionCover_isClosed S U c g₀ i
    (((freePresheaf S).map (closedSubLightProfiniteι C hC).op c).support.card <
      c.support.card) := by
  classical
  dsimp only
  apply freePresheaf_restrict_support_card_lt_of_eq_on_pair S
    (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
      (freePresheaf_collisionCover_isClosed S U c g₀ i)) c i.2.1 hg₀ i.2.2
  ext x
  change (show U ⟶ S from i.1)
      (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x) =
    g₀ (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x)
  rw [closedSubLightProfiniteι_apply]
  exact (x : freePresheaf_collisionCoverSet S U c g₀ i).2

/--
@isnad1 id=mem.1h4v.s10.805acd4757e9 from=translated src=- shape=ab8a1969 vocab=316e97f6
-/
lemma freePresheafToTopologicalFreePresheaf_equalizerSieve_mem
    (S U : LightProfinite.{0})
    (a b : (freePresheaf S).obj ⟨U⟩)
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b) :
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U := by
  classical
  let P : ℕ → Prop := fun n => ∀ (U : LightProfinite.{0})
      (a b : (freePresheaf S).obj ⟨U⟩),
    (a - b).support.card = n →
    (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b →
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U
  have hind : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U a b hcard h
      by_cases hn : n = 0
      · have hcard0 : (a - b).support.card = 0 := hcard.trans hn
        have hempty : (a - b).support = ∅ := Finset.card_eq_zero.mp hcard0
        have hsub : a - b = 0 := Finsupp.support_eq_empty.mp hempty
        have hab : a = b := sub_eq_zero.mp hsub
        subst b
        rw [CategoryTheory.Presheaf.equalizerSieve_self_eq_top]
        exact (coherentTopology LightProfinite).top_mem U
      · have hcard_ne : (a - b).support.card ≠ 0 := by
          intro hzero
          exact hn (hcard.symm.trans hzero)
        obtain ⟨g₀, hg₀⟩ :=
          (Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne) : (a - b).support.Nonempty)
        let c : (freePresheaf S).obj ⟨U⟩ := a - b
        have hg₀c : g₀ ∈ c.support := by
          change g₀ ∈ (a - b).support
          exact hg₀
        let I := freePresheaf_collisionCoverIndex S U c g₀
        haveI : Finite I := freePresheaf_collisionCoverIndex_finite S U c g₀
        let C : I → Set U := freePresheaf_collisionCoverSet S U c g₀
        let hC : ∀ i, IsClosed (C i) := freePresheaf_collisionCover_isClosed S U c g₀
        have hzero : ∀ u : U, Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0 := by
          intro u
          simpa [c] using
            freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero S U h u
        have hcover : ∀ u : U, ∃ i, u ∈ C i := by
          simpa [c, C] using
            freePresheaf_collisionCover_covers_of_pointwise_zero S U c hg₀c hzero
        refine presheaf_equalizerSieve_mem_of_finite_closed_cover_locally a b C hC hcover ?_
        intro i
        let V : LightProfinite.{0} := closedSubLightProfinite (C i) (hC i)
        let π : V ⟶ U := closedSubLightProfiniteι (C i) (hC i)
        let aV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op a
        let bV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op b
        have hres : (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ aV =
            (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ bV := by
          exact (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op a).trans
            ((congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
              (topologicalFreePresheaf S).map π.op z) h).trans
            (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op b).symm)
        have hdropc : (((freePresheaf S).map π.op c).support.card < c.support.card) := by
          simpa [c, I, C, hC, V, π] using
            freePresheaf_collisionCover_restrict_card_lt S U c hg₀c i
        have hmap_sub : (freePresheaf S).map π.op c = aV - bV := by
          exact freePresheaf_map_sub S π a b
        have hdrop : (aV - bV).support.card < n := by
          calc
            (aV - bV).support.card = ((freePresheaf S).map π.op c).support.card := by
              rw [← hmap_sub]
            _ < c.support.card := hdropc
            _ = n := by simpa [c] using hcard
        exact ih (aV - bV).support.card hdrop V aV bV rfl hres
  exact hind (a - b).support.card U a b rfl h

/--
@isnad1 id=islocall.0h1v.s7.bdf1c53dd9df from=translated src=- shape=b590788d vocab=2dcd97df
-/
instance freePresheafToTopologicalFreePresheaf_isLocallyInjective
    (S : LightProfinite.{0}) :
    CategoryTheory.Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  refine ⟨?_⟩
  intro Uop a b h
  rcases Uop with ⟨U⟩
  change CategoryTheory.Presheaf.equalizerSieve a b ∈ (coherentTopology LightProfinite) U
  exact freePresheafToTopologicalFreePresheaf_equalizerSieve_mem S U a b h

end LightCondAb
