/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Tengoku

/-!
# Left and right limits within a set
-/

@[expose] public section

open Set Filter

open Topology

/--
@isnad1 id=eq.0h4v.s5.f7ff1639d4be from=translated src=- shape=c2167df9 vocab=645b83b0
-/
lemma nhdsWithin_inf_principal {E : Type*} [TopologicalSpace E] (s t : Set E) (x : E) :
    𝓝[s] x ⊓ 𝓟 t = 𝓝[s ∩ t] x := by
  rw [nhdsWithin, nhdsWithin, inf_assoc, inf_principal, Set.inter_comm]

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLimWithin (f : α → β) (s : Set α) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[Set.Iio a ∩ s] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[Set.Iio a ∩ s] a) (𝓝 y) then f a else
    limUnder (𝓝[Set.Iio a ∩ s] a) f

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLimWithin (f : α → β) (s : Set α) (a : α) : β :=
  @Function.leftLimWithin αᵒᵈ β _ _ f s a

open Function

/-! ### The within-neighbourhood filter is `NeBot` under a density hypothesis -/

/-- If `s` is dense and `𝓝[<] a` is not bot, then `a` is a left-accumulation point of `s`.
@isnad1 id=nebot.1h3v.s6.58b686aa542a from=translated src=- shape=824b8daa vocab=e73187e6
-/
lemma nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[<] a).NeBot] :
    (𝓝[Iio a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Iio a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Iio) hne
  exact ⟨x, hx.1, hx.2, hxs⟩

/-- If `s` is dense and `a` is not a minimum, then `a` is a left-accumulation point of `s`.
@isnad1 id=nebot.1h3v.s6.3ad20f01e610 from=translated src=- shape=7646f135 vocab=1ff07b12
-/
lemma nhdsWithin_Iio_inter_neBot [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [NoMinOrder α] {s : Set α} (hs : Dense s) (a : α) : (𝓝[Iio a ∩ s] a).NeBot :=
  nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot hs a

/-- If `s` is dense and `𝓝[>] a` is not bot, then `a` is a right-accumulation point of `s`.
@isnad1 id=nebot.1h3v.s6.d529c747b499 from=translated src=- shape=824b8daa vocab=448dfa55
-/
lemma nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[>] a).NeBot] :
    (𝓝[Ioi a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Ioi a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Ioi) hne
  exact ⟨x, hx.1, hx.2, hxs⟩

/-- If `s` is dense and `a` is not a maximum, then `a` is a right-accumulation point of `s`.
@isnad1 id=nebot.1h3v.s6.1b3d45e2a7fb from=translated src=- shape=7646f135 vocab=669db35c
-/
lemma nhdsWithin_Ioi_inter_neBot [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [NoMaxOrder α] {s : Set α} (hs : Dense s) (a : α) : (𝓝[Ioi a ∩ s] a).NeBot :=
  nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hs a

/-! ### Basic characterisations of the within left/right limit -/

/--
@isnad1 id=eq.1h6v.s6.c4967af3862a from=translated src=- shape=933f0a99 vocab=f1a6afdd
-/
lemma leftLimWithin_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} {y : β} [h : (𝓝[Iio a ∩ s] a).NeBot]
    (h' : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) :
    leftLimWithin f s a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLimWithin, neBot_iff.mp h, h'', not_true, or_self_iff, ite_false]
  exact lim_eq h'

/--
@isnad1 id=eq.1h6v.s6.034dc5320258 from=translated src=- shape=933f0a99 vocab=db66cc96
-/
lemma rightLimWithin_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} {y : β} [h : (𝓝[Ioi a ∩ s] a).NeBot]
    (h' : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) :
    rightLimWithin f s a = y :=
  leftLimWithin_eq_of_tendsto (α := αᵒᵈ) (h := h) h'

/--
@isnad1 id=eq.1h5v.s6.9b9fd6754485 from=translated src=- shape=ca198ca8 vocab=38717f89
-/
lemma leftLimWithin_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Iio a ∩ s] a = ⊥) : leftLimWithin f s a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLimWithin, h]

/--
@isnad1 id=eq.1h5v.s6.a246fbd9c2bc from=translated src=- shape=ca198ca8 vocab=d557f22f
-/
lemma rightLimWithin_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Ioi a ∩ s] a = ⊥) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_eq_bot (α := αᵒᵈ) f h

/--
@isnad1 id=eq.1h5v.s6.997b654eac2d from=translated src=- shape=092b2391 vocab=8ea3aa9f
-/
lemma leftLimWithin_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {s : Set α} {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) : leftLimWithin f s a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLimWithin, h]

/--
@isnad1 id=eq.1h5v.s6.ffef2b4e47c3 from=translated src=- shape=092b2391 vocab=91689e28
-/
lemma rightLimWithin_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {s : Set α} {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_not_tendsto (α := αᵒᵈ) f h

/--
@isnad1 id=eq.1h5v.s5.19194e0e62f2 from=translated src=- shape=d3d75edb vocab=32bb96d6
-/
lemma leftLimWithin_eq_of_isBot {f : α → β} {s : Set α} {a : α} (ha : IsBot a) :
    leftLimWithin f s a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLimWithin_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

/--
@isnad1 id=eq.1h5v.s5.08738783c147 from=translated src=- shape=d3d75edb vocab=4d28682d
-/
lemma rightLimWithin_eq_of_isTop {f : α → β} {s : Set α} {a : α} (ha : IsTop a) :
    rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_isBot (α := αᵒᵈ) ha

/--
@isnad1 id=eq.1h5v.s6.7802f327d3f4 from=translated src=- shape=d29ac197 vocab=6e33f832
-/
lemma ContinuousWithinAt.leftLimWithin_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} (hf : ContinuousWithinAt f (Iic a ∩ s) a) :
    leftLimWithin f s a = f a := by
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [leftLimWithin_eq_of_eq_bot f h']
  apply leftLimWithin_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ Iio_subset_Iic_self))

/--
@isnad1 id=eq.1h5v.s6.5e47d9019ed3 from=translated src=- shape=d29ac197 vocab=21cbbb50
-/
lemma ContinuousWithinAt.rightLimWithin_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} (hf : ContinuousWithinAt f (Ici a ∩ s) a) :
    rightLimWithin f s a = f a :=
  ContinuousWithinAt.leftLimWithin_eq (α := αᵒᵈ) hf

/--
@isnad1 id=tendsto.1h5v.s6.312789b7eba5 from=translated src=- shape=c3e938b8 vocab=8ea3aa9f
-/
lemma tendsto_leftLimWithin_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)) := by
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLimWithin, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

/--
@isnad1 id=tendsto.1h5v.s6.7ce1990867b1 from=translated src=- shape=c3e938b8 vocab=91689e28
-/
lemma tendsto_rightLimWithin_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)) :=
  tendsto_leftLimWithin_of_tendsto (α := αᵒᵈ) h

/-- The within left limit is a cluster point of `f` along the closed left within-neighbourhood,
provided `a ∈ s`.
@isnad1 id=mapclust.1h5v.s6.c0c5f7f2e64c from=translated src=- shape=de9a0880 vocab=af736ba4
-/
lemma mapClusterPt_leftLimWithin [TopologicalSpace α] [OrderTopology α]
    (f : α → β) {s : Set α} {a : α} (ha : a ∈ s) :
    MapClusterPt (leftLimWithin f s a) (𝓝[Iic a ∩ s] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[Iic a ∩ s] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun t ht t' ht' ↦ ?_)
    refine ⟨f a, mem_of_mem_nhds ht, ?_⟩
    simp only [mem_map] at ht'
    apply mem_of_mem_nhdsWithin (show a ∈ Iic a ∩ s from ⟨le_refl a, ha⟩) ht'
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLimWithin_eq_of_eq_bot, A]
  by_cases! H : ¬ ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLimWithin_eq_of_not_tendsto, A]
  have : MapClusterPt (leftLimWithin f s a) (𝓝[Iio a ∩ s] a) f :=
    (tendsto_leftLimWithin_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ (inter_subset_inter_left _ Iio_subset_Iic_self))

/--
@isnad1 id=mapclust.1h5v.s6.27dc6b6ee505 from=translated src=- shape=de9a0880 vocab=33a5dacc
-/
lemma mapClusterPt_rightLimWithin [TopologicalSpace α] [OrderTopology α]
    (f : α → β) {s : Set α} {a : α} (ha : a ∈ s) :
    MapClusterPt (rightLimWithin f s a) (𝓝[Ici a ∩ s] a) f :=
  mapClusterPt_leftLimWithin (α := αᵒᵈ) f ha

/-! ### Regularisation: the within left/right limit is one-sided continuous within `s`

These mirror the original `continuousWithinAt_leftLim_Iic` etc.: they take only the single-point
hypothesis that `f` admits a within left (resp. right) limit at `a`, and split into cases according
to whether the within-neighbourhood at each nearby point is `⊥`, has no limit, or has a limit. The
conclusions are stated *within* `s` (`Iic a ∩ s` in place of `Iic a`); restricting to `s` is what
lets the degenerate cases go through, so no density hypothesis is needed. -/

/--
@isnad1 id=continuo.1h5v.s6.00bfc08ba8b4 from=translated src=- shape=9807a16f vocab=4b35aa67
-/
lemma continuousWithinAt_leftLimWithin_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    ContinuousWithinAt (leftLimWithin f s) (Iic a ∩ s) a := by
  have hsub : Iic a ∩ s ⊆ (Iio a ∩ s) ∪ {a} := by
    rintro x ⟨hx1, hx2⟩
    rcases lt_or_eq_of_le hx1 with hlt | heq
    · exact Or.inl ⟨hlt, hx2⟩
    · exact Or.inr heq
  rw [ContinuousWithinAt]
  refine Tendsto.mono_left ?_ (nhdsWithin_mono a hsub)
  rw [nhdsWithin_union, nhdsWithin_singleton, tendsto_sup]
  refine ⟨?_, tendsto_pure_nhds _ _⟩
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
    (Filter.nonempty_of_mem (show Iio a ∩ s ∈ 𝓝[Iio a ∩ s] a from self_mem_nhdsWithin)).mono
      inter_subset_left
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt ⟨b, hb⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [nhdsWithin_mono a inter_subset_left (Ioo_mem_nhdsLT hua), self_mem_nhdsWithin]
    with c hc hcs
  rcases eq_or_neBot (𝓝[Iio c ∩ s] c) with h'c | h'c
  · simpa [h'c, leftLimWithin_eq_of_eq_bot] using hu hc hcs.2
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 y)
  · simpa [leftLimWithin_eq_of_not_tendsto _ h''c] using hu hc hcs.2
  apply V_closed.mem_of_tendsto (tendsto_leftLimWithin_of_tendsto h''c)
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsLT hc.1] with d hd hds
  exact hu ⟨hd.1, hd.2.trans hc.2⟩ hds

/--
@isnad1 id=continuo.1h5v.s6.1b8222617e5e from=translated src=- shape=9807a16f vocab=b2be1e56
-/
lemma continuousWithinAt_rightLimWithin_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    ContinuousWithinAt (rightLimWithin f s) (Ici a ∩ s) a :=
  continuousWithinAt_leftLimWithin_Iic (α := αᵒᵈ) h

/-- Dense version of `continuousWithinAt_leftLimWithin_Iic` with the stronger conclusion that the
regularisation is continuous along the *full* left neighbourhood `Iic a`. This needs `s` dense (so
that the within-neighbourhood is `NeBot`), the single-point hypothesis `h` that `f` has a within
left limit at `a`, and that `f` has a within left limit at every point eventually to the left of
`a`.
@isnad1 id=continuo.3h5v.s7.8cc214d2aec3 from=translated src=- shape=696afe4d vocab=60b1af32
-/
lemma continuousWithinAt_leftLimWithin_Iic_of_dense [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMinOrder α] [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[<] a, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c))) :
    ContinuousWithinAt (leftLimWithin f s) (Iic a) a := by
  have hsplit : 𝓝[≤] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, hsplit, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt (exists_lt a)).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hua, hlim] with c hc hlimc
  have hne := nhdsWithin_Iio_inter_neBot hs c
  refine V_closed.mem_of_tendsto hlimc ?_
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsLT hc.1] with x hx hxs
  exact hu ⟨hx.1, hx.2.trans hc.2⟩ hxs

/-- Dense version of `continuousWithinAt_rightLimWithin_Ici` with
the stronger conclusion `Ici a`.
@isnad1 id=continuo.3h5v.s7.c2feac56de51 from=translated src=- shape=696afe4d vocab=c5a5d847
-/
lemma continuousWithinAt_rightLimWithin_Ici_of_dense [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[>] a, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c))) :
    ContinuousWithinAt (rightLimWithin f s) (Ici a) a :=
  continuousWithinAt_leftLimWithin_Iic_of_dense (α := αᵒᵈ) hs h hlim

/--
@isnad1 id=eq.1h5v.s6.a97bea96500b from=translated src=- shape=3433d756 vocab=c62c0841
-/
lemma leftLimWithin_leftLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    leftLimWithin (leftLimWithin f s) s a = leftLimWithin f s a :=
  (continuousWithinAt_leftLimWithin_Iic h).leftLimWithin_eq

/--
@isnad1 id=eq.1h5v.s6.5de813ea2f1e from=translated src=- shape=3433d756 vocab=af08630e
-/
lemma rightLimWithin_rightLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    rightLimWithin (rightLimWithin f s) s a = rightLimWithin f s a :=
  leftLimWithin_leftLimWithin (α := αᵒᵈ) h

/--
@isnad1 id=eq.1h5v.s7.a067916d806a from=translated src=- shape=668afaac vocab=a98e9931
-/
lemma leftLimWithin_rightLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α} [h' : (𝓝[Iio a ∩ s] a).NeBot]
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    leftLimWithin (rightLimWithin f s) s a = leftLimWithin f s a := by
  apply leftLimWithin_eq_of_tendsto
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
    (Filter.nonempty_of_mem (show Iio a ∩ s ∈ 𝓝[Iio a ∩ s] a from self_mem_nhdsWithin)).mono
      inter_subset_left
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt ⟨b, hb⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [nhdsWithin_mono a inter_subset_left (Ioo_mem_nhdsLT hua), self_mem_nhdsWithin]
    with c hc hcs
  rcases eq_or_neBot (𝓝[Ioi c ∩ s] c) with h'c | h'c
  · simpa [h'c, rightLimWithin_eq_of_eq_bot] using hu hc hcs.2
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 y)
  · simpa [rightLimWithin_eq_of_not_tendsto _ h''c] using hu hc hcs.2
  apply V_closed.mem_of_tendsto (tendsto_rightLimWithin_of_tendsto h''c)
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hc.2] with d hd hds
  exact hu ⟨hc.1.trans hd.1, hd.2⟩ hds

/--
@isnad1 id=eq.1h5v.s7.a3bee864919c from=translated src=- shape=668afaac vocab=66f9d61e
-/
lemma rightLimWithin_leftLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α} [h' : (𝓝[Ioi a ∩ s] a).NeBot]
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    rightLimWithin (leftLimWithin f s) s a = rightLimWithin f s a :=
  leftLimWithin_rightLimWithin (α := αᵒᵈ) (h' := h') h

/-! ### Behaviour at infinity -/

/--
@isnad1 id=tendsto.3h5v.s7.8f5e7823f22d from=translated src=- shape=948f23a3 vocab=a8218472
-/
lemma tendsto_leftLimWithin_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMinOrder α] [NoTopOrder α]
    [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c)))
    (h : Tendsto f atTop (𝓝 b)) :
    Tendsto (leftLimWithin f s) atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  have := nhdsWithin_Iio_inter_neBot hs x
  exact ((hlim x).mapClusterPt).mono nhdsWithin_le_nhds

/--
@isnad1 id=tendsto.3h5v.s7.e624f5d9c2f7 from=translated src=- shape=a249d7b0 vocab=c017dfe1
-/
lemma tendsto_rightLimWithin_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c)))
    (h : Tendsto f atTop (𝓝 b)) :
    Tendsto (rightLimWithin f s) atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : rightLimWithin f s ⊤ = f ⊤ := rightLimWithin_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    have := nhdsWithin_Ioi_inter_neBot hs x
    exact ((hlim x).mapClusterPt).mono nhdsWithin_le_nhds

/--
@isnad1 id=tendsto.3h5v.s7.3563948f5cdd from=translated src=- shape=948f23a3 vocab=804131ac
-/
lemma tendsto_rightLimWithin_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] [NoBotOrder α]
    [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c)))
    (h : Tendsto f atBot (𝓝 b)) :
    Tendsto (rightLimWithin f s) atBot (𝓝 b) :=
  tendsto_leftLimWithin_atTop_of_tendsto (α := αᵒᵈ) hs hlim h

/--
@isnad1 id=tendsto.3h5v.s7.fa7d807c423f from=translated src=- shape=a249d7b0 vocab=3e0c5a93
-/
lemma tendsto_leftLimWithin_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMinOrder α] [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c)))
    (h : Tendsto f atBot (𝓝 b)) :
    Tendsto (leftLimWithin f s) atBot (𝓝 b) :=
  tendsto_rightLimWithin_atTop_of_tendsto (α := αᵒᵈ) hs hlim h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {s : Set α} {x y : α}
include hf

/-- For a monotone function, the within left limit is the supremum of the values to the left.
Note that the supremum is over the whole `Iio x`, not just `Iio x ∩ s`: any subset of `Iio x`
accumulating at `x` yields the same limit.
@isnad1 id=eq.1h5v.s7.929f16979c9e from=translated src=- shape=12ffea4a vocab=aa4c011b
-/
lemma leftLimWithin_eq_sSup [TopologicalSpace α] [OrderTopology α]
    [(𝓝[Iio x ∩ s] x).NeBot] : leftLimWithin f s x = sSup (f '' Iio x) :=
  leftLimWithin_eq_of_tendsto
    ((hf.tendsto_nhdsLT x).mono_left (nhdsWithin_mono x inter_subset_left))

/--
@isnad1 id=eq.1h5v.s7.24f2d9db2235 from=translated src=- shape=12ffea4a vocab=943a46a8
-/
lemma rightLimWithin_eq_sInf [TopologicalSpace α] [OrderTopology α]
    [(𝓝[Ioi x ∩ s] x).NeBot] : rightLimWithin f s x = sInf (f '' Ioi x) :=
  rightLimWithin_eq_of_tendsto
    ((hf.tendsto_nhdsGT x).mono_left (nhdsWithin_mono x inter_subset_left))

/--
@isnad1 id=le.2h6v.s6.c2cabb9b0a04 from=translated src=- shape=c6853b69 vocab=607599ca
-/
lemma leftLimWithin_le (h : x ≤ y) : leftLimWithin f s x ≤ f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio x ∩ s] x) with h' | h'
  · simpa [leftLimWithin, h'] using hf h
  rw [leftLimWithin_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact ((forall_mem_nonempty_iff_neBot.2 h') _ self_mem_nhdsWithin).mono inter_subset_left
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)

/--
@isnad1 id=le.2h6v.s6.9ee6f067d226 from=translated src=- shape=8fd78dc7 vocab=2be89488
-/
lemma le_leftLimWithin (h : x < y) : f x ≤ leftLimWithin f s y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio y ∩ s] y) with h' | h'
  · rw [leftLimWithin_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLimWithin_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro z hz
  exact hf hz.le

/--
@isnad1 id=monotone.1h4v.s6.2838bdb5f02f from=translated src=- shape=d81da962 vocab=68d918d1
-/
@[gcongr, mono]
protected lemma leftLimWithin : Monotone (leftLimWithin f s) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLimWithin_le le_rfl).trans (hf.le_leftLimWithin hxy)

/--
@isnad1 id=le.2h6v.s6.909e085b221d from=translated src=- shape=4809f016 vocab=0708ee63
-/
lemma le_rightLimWithin (h : x ≤ y) : f x ≤ rightLimWithin f s y :=
  hf.dual.leftLimWithin_le h

/--
@isnad1 id=le.2h6v.s6.8b02863b26c3 from=translated src=- shape=b6b38b9e vocab=1e91b182
-/
lemma rightLimWithin_le (h : x < y) : rightLimWithin f s x ≤ f y :=
  hf.dual.le_leftLimWithin h

/--
@isnad1 id=monotone.1h4v.s6.4081902f62be from=translated src=- shape=d81da962 vocab=210d1f73
-/
@[gcongr, mono]
protected lemma rightLimWithin : Monotone (rightLimWithin f s) :=
  fun _ _ h => hf.dual.leftLimWithin h

/--
@isnad1 id=le.2h6v.s6.faf2dab441ce from=translated src=- shape=09d54d08 vocab=ac44c719
-/
lemma leftLimWithin_le_rightLimWithin (h : x ≤ y) :
    leftLimWithin f s x ≤ rightLimWithin f s y :=
  (hf.leftLimWithin_le le_rfl).trans (hf.le_rightLimWithin h)

/--
@isnad1 id=le.2h6v.s6.5e4cf9234d74 from=translated src=- shape=6d4f1215 vocab=4cc1fab9
-/
lemma rightLimWithin_le_leftLimWithin (h : x < y) :
    rightLimWithin f s x ≤ leftLimWithin f s y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio y ∩ s] y) with (h' | h')
  · simpa [leftLimWithin, h'] using rightLimWithin_le hf h
  have h'' : (𝓝[<] y).NeBot := h'.mono (nhdsWithin_mono y inter_subset_left)
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLimWithin f s x ≤ f a := hf.rightLimWithin_le xa
    _ ≤ leftLimWithin f s y := hf.le_leftLimWithin ay

variable [TopologicalSpace α] [OrderTopology α]

/--
@isnad1 id=tendsto.1h5v.s6.6cf787f32913 from=translated src=- shape=d7d9c1a1 vocab=98e11984
-/
lemma tendsto_leftLimWithin (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝 (leftLimWithin f s x)) :=
  tendsto_leftLimWithin_of_tendsto
    ⟨_, (hf.tendsto_nhdsLT x).mono_left (nhdsWithin_mono x inter_subset_left)⟩

/--
@isnad1 id=tendsto.1h5v.s7.f2083fd49517 from=translated src=- shape=ad1f94e0 vocab=6cc84c9a
-/
lemma tendsto_leftLimWithin_within (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝[≤] leftLimWithin f s x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLimWithin x)
  filter_upwards [self_mem_nhdsWithin] with y hy using hf.le_leftLimWithin hy.1

/--
@isnad1 id=tendsto.1h5v.s6.d4678d87662f from=translated src=- shape=d7d9c1a1 vocab=d7dbf6f0
-/
lemma tendsto_rightLimWithin (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝 (rightLimWithin f s x)) :=
  hf.dual.tendsto_leftLimWithin x

/--
@isnad1 id=tendsto.1h5v.s7.190f73e72fcf from=translated src=- shape=ad1f94e0 vocab=7fa4b1ea
-/
lemma tendsto_rightLimWithin_within (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝[≥] rightLimWithin f s x) :=
  hf.dual.tendsto_leftLimWithin_within x

/-- A monotone function is continuous to the left within `s` at `x` if and only if its within left
limit coincides with the value of the function.
@isnad1 id=iff.1h5v.s6.bcf56f3669e8 from=translated src=- shape=64f4b84b vocab=787cc0b0
-/
lemma continuousWithinAt_Iio_iff_leftLimWithin_eq :
    ContinuousWithinAt f (Iio x ∩ s) x ↔ leftLimWithin f s x = f x := by
  rcases eq_or_neBot (𝓝[Iio x ∩ s] x) with h' | h'
  · simp [leftLimWithin_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLimWithin x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLimWithin (s := s) x
  rwa [h] at this

/-- A monotone function is continuous to the right within `s` at `x` if and only if its within
right limit coincides with the value of the function.
@isnad1 id=iff.1h5v.s6.f1c1bd1baac8 from=translated src=- shape=64f4b84b vocab=07c6b55d
-/
lemma continuousWithinAt_Ioi_iff_rightLimWithin_eq :
    ContinuousWithinAt f (Ioi x ∩ s) x ↔ rightLimWithin f s x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLimWithin_eq

/-- A monotone function is continuous within `s` at `x` if and only if its within left and right
limits coincide. This is the within-set analogue of `continuousAt_iff_leftLim_eq_rightLim`, using
`ContinuousWithinAt f s x` in place of the full `ContinuousAt f x`.
@isnad1 id=iff.1h5v.s6.46b741f3fd02 from=translated src=- shape=eccfc257 vocab=f866badf
-/
lemma continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin :
    ContinuousWithinAt f s x ↔ leftLimWithin f s x = rightLimWithin f s x := by
  have hdecomp : ContinuousWithinAt f s x ↔
      leftLimWithin f s x = f x ∧ rightLimWithin f s x = f x := by
    rw [← hf.continuousWithinAt_Iio_iff_leftLimWithin_eq,
      ← hf.continuousWithinAt_Ioi_iff_rightLimWithin_eq]
    refine ⟨fun h => ⟨h.mono inter_subset_right, h.mono inter_subset_right⟩, fun ⟨hL, hR⟩ => ?_⟩
    refine ((hL.union hR).union continuousWithinAt_singleton).mono ?_
    intro y hy
    rcases lt_trichotomy y x with hlt | heq | hgt
    · exact Or.inl (Or.inl ⟨hlt, hy⟩)
    · exact Or.inr heq
    · exact Or.inl (Or.inr ⟨hgt, hy⟩)
  rw [hdecomp]
  refine ⟨fun ⟨hL, hR⟩ => by rw [hL, hR], fun h => ?_⟩
  have hle : leftLimWithin f s x ≤ f x := hf.leftLimWithin_le le_rfl
  have hge : f x ≤ rightLimWithin f s x := hf.le_rightLimWithin le_rfl
  have hRfx : rightLimWithin f s x = f x := le_antisymm (h ▸ hle) hge
  exact ⟨h.trans hRfx, hRfx⟩

/-- A monotone function is continuous at `x` (for the full topology) if and only if its within left
and right limits along a *dense* set `s` coincide. Density is used to recover continuity along the
full neighbourhood `𝓝 x` from the within-`s` neighbourhoods.
@isnad1 id=iff.2h5v.s7.64da1a42fac4 from=translated src=- shape=4c50010a vocab=e3055e5d
-/
lemma continuousAt_iff_leftLimWithin_eq_rightLimWithin
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] (hs : Dense s) :
    ContinuousAt f x ↔ leftLimWithin f s x = rightLimWithin f s x := by
  refine ⟨fun h => (hf.continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin).1
    h.continuousWithinAt, fun h => ?_⟩
  have hL : (𝓝[Iio x ∩ s] x).NeBot := nhdsWithin_Iio_inter_neBot hs x
  have hR : (𝓝[Ioi x ∩ s] x).NeBot := nhdsWithin_Ioi_inter_neBot hs x
  have hle : leftLimWithin f s x ≤ f x := hf.leftLimWithin_le le_rfl
  have hge : f x ≤ rightLimWithin f s x := hf.le_rightLimWithin le_rfl
  have hRfx : rightLimWithin f s x = f x := le_antisymm (h ▸ hle) hge
  have hLfx : leftLimWithin f s x = f x := h.trans hRfx
  have hsupL : sSup (f '' Iio x) = f x := (hf.leftLimWithin_eq_sSup (s := s)).symm.trans hLfx
  have hsupR : sInf (f '' Ioi x) = f x := (hf.rightLimWithin_eq_sInf (s := s)).symm.trans hRfx
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · have ht := hf.tendsto_nhdsLT x
    rw [hsupL] at ht
    exact ht
  · have ht := hf.tendsto_nhdsGT x
    rw [hsupR] at ht
    exact ht

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {s : Set α} {x y : α}
include hf

/--
@isnad1 id=le.2h6v.s6.b13557bbf5b2 from=translated src=- shape=198bc06a vocab=eb07c865
-/
lemma le_leftLimWithin (h : x ≤ y) : f y ≤ leftLimWithin f s x :=
  hf.dual_right.leftLimWithin_le h

/--
@isnad1 id=le.2h6v.s6.257f695f8303 from=translated src=- shape=dd98877b vocab=f2c428c8
-/
lemma leftLimWithin_le (h : x < y) : leftLimWithin f s y ≤ f x :=
  hf.dual_right.le_leftLimWithin h

/--
@isnad1 id=antitone.1h4v.s6.595273ba966b from=translated src=- shape=d81da962 vocab=39dbe4f6
-/
@[gcongr, mono]
protected lemma leftLimWithin : Antitone (leftLimWithin f s) :=
  hf.dual_right.leftLimWithin

/--
@isnad1 id=le.2h6v.s6.14600f21a629 from=translated src=- shape=e13bbb8a vocab=da82d24d
-/
lemma rightLimWithin_le (h : x ≤ y) : rightLimWithin f s y ≤ f x :=
  hf.dual_right.le_rightLimWithin h

/--
@isnad1 id=le.2h6v.s6.f48e23da8e50 from=translated src=- shape=1553f2c6 vocab=39f7ee33
-/
lemma le_rightLimWithin (h : x < y) : f y ≤ rightLimWithin f s x :=
  hf.dual_right.rightLimWithin_le h

/--
@isnad1 id=antitone.1h4v.s6.ff3920efad1e from=translated src=- shape=d81da962 vocab=1a05fbd6
-/
@[gcongr, mono]
protected lemma rightLimWithin : Antitone (rightLimWithin f s) :=
  hf.dual_right.rightLimWithin

/--
@isnad1 id=le.2h6v.s6.77497086f946 from=translated src=- shape=85085461 vocab=2db3feeb
-/
lemma rightLimWithin_le_leftLimWithin (h : x ≤ y) :
    rightLimWithin f s y ≤ leftLimWithin f s x :=
  hf.dual_right.leftLimWithin_le_rightLimWithin h

/--
@isnad1 id=le.2h6v.s6.320ed403bc1a from=translated src=- shape=0b2c4891 vocab=e7e5f51a
-/
lemma leftLimWithin_le_rightLimWithin (h : x < y) :
    leftLimWithin f s y ≤ rightLimWithin f s x :=
  hf.dual_right.rightLimWithin_le_leftLimWithin h

variable [TopologicalSpace α] [OrderTopology α]

/--
@isnad1 id=tendsto.1h5v.s6.c04272f02720 from=translated src=- shape=d7d9c1a1 vocab=78614ae8
-/
lemma tendsto_leftLimWithin (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝 (leftLimWithin f s x)) :=
  hf.dual_right.tendsto_leftLimWithin x

/--
@isnad1 id=tendsto.1h5v.s7.77ef4a4b1968 from=translated src=- shape=ad1f94e0 vocab=117009f9
-/
lemma tendsto_leftLimWithin_within (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝[≥] leftLimWithin f s x) :=
  hf.dual_right.tendsto_leftLimWithin_within x

/--
@isnad1 id=tendsto.1h5v.s6.d3df18b00b81 from=translated src=- shape=d7d9c1a1 vocab=75adb00f
-/
lemma tendsto_rightLimWithin (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝 (rightLimWithin f s x)) :=
  hf.dual_right.tendsto_rightLimWithin x

/--
@isnad1 id=tendsto.1h5v.s7.b187d489481a from=translated src=- shape=ad1f94e0 vocab=dca7b9e6
-/
lemma tendsto_rightLimWithin_within (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝[≤] rightLimWithin f s x) :=
  hf.dual_right.tendsto_rightLimWithin_within x

/-- An antitone function is continuous to the left within `s` at `x` if and only if its within left
limit coincides with the value of the function.
@isnad1 id=iff.1h5v.s6.089f063adf89 from=translated src=- shape=64f4b84b vocab=6c8a34f5
-/
lemma continuousWithinAt_Iio_iff_leftLimWithin_eq :
    ContinuousWithinAt f (Iio x ∩ s) x ↔ leftLimWithin f s x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLimWithin_eq

/-- An antitone function is continuous to the right within `s` at `x` if and only if its within
right limit coincides with the value of the function.
@isnad1 id=iff.1h5v.s6.9a70243115c1 from=translated src=- shape=64f4b84b vocab=c5d60db2
-/
lemma continuousWithinAt_Ioi_iff_rightLimWithin_eq :
    ContinuousWithinAt f (Ioi x ∩ s) x ↔ rightLimWithin f s x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLimWithin_eq

/-- An antitone function is continuous within `s` at `x` if and only if its within left and right
limits coincide.
@isnad1 id=iff.1h5v.s6.5e4fc521c596 from=translated src=- shape=eccfc257 vocab=6a5ac30a
-/
lemma continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin :
    ContinuousWithinAt f s x ↔ leftLimWithin f s x = rightLimWithin f s x :=
  hf.dual_right.continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin

/-- An antitone function is continuous at `x` (for the full topology) if and only if its within left
and right limits along a *dense* set `s` coincide.
@isnad1 id=iff.2h5v.s7.640a5f93764d from=translated src=- shape=4c50010a vocab=ed7247da
-/
lemma continuousAt_iff_leftLimWithin_eq_rightLimWithin
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] (hs : Dense s) :
    ContinuousAt f x ↔ leftLimWithin f s x = rightLimWithin f s x :=
  hf.dual_right.continuousAt_iff_leftLimWithin_eq_rightLimWithin hs

end Antitone
