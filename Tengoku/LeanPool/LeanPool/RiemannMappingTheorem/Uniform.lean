/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Tengoku

/-!
# LeanPool.RiemannMappingTheorem.Uniform
-/

@[expose] public section

open Set Filter UniformSpace Function Uniformity Topology SetRel

variable {ι α β : Type*} {a : α} {s t : Set α} {x u v : Set (α × α)}

/--
@isnad1 id=issymm.1h2v.s5.0bf5f396c3b4 from=translated src=- shape=7469a5cf vocab=6d76ee2b
-/
lemma symmetricRel_of (h : ∀ {a b : α}, (a, b) ∈ x → (b, a) ∈ x) : SetRel.IsSymm x where
  symm _ _ := h

namespace UniformSpace -- uniform thickening

/-- The `U`-thickening of `S`: the union of `U`-balls around each point of
`S`. Equals `{a | ∃ x ∈ S, (x, a) ∈ U}`. -/
def thickening (U : Set (α × α)) (S : Set α) : Set α := ⋃ x ∈ S, ball x U

/--
@isnad1 id=iff.0h4v.s5.7f98961ff08d from=translated src=- shape=0b63e59e vocab=faffd99d
-/
lemma mem_thickening : a ∈ thickening u s ↔ ∃ x ∈ s, (x, a) ∈ u := by
  simp only [thickening, ball, mem_iUnion, Set.mem_preimage, exists_prop]

/--
@isnad1 id=eq.0h3v.s4.130f671c93f7 from=translated src=- shape=9e69d6ef vocab=55cb0ef0
-/
@[simp] lemma thickening_singleton : thickening u {a} = ball a u := by
  simp only [thickening, mem_singleton_iff, iUnion_iUnion_eq_left]

/--
@isnad1 id=monotone.0h2v.s6.839e3e4628c5 from=translated src=- shape=c6af5a62 vocab=fc737c11
-/
@[simp] lemma monotone_thickening : Monotone (thickening · s) := by
  intro u v huv
  apply iUnion₂_mono
  simp only [ball] at huv ⊢
  exact fun _ _ => preimage_mono huv

/--
@isnad1 id=monotone.0h2v.s5.71ea04963dcd from=translated src=- shape=997b0354 vocab=fc737c11
-/
lemma thickening_mono : Monotone (thickening u) :=
  fun _ _ h => iUnion₂_mono' (fun a ha => ⟨a, h ha, subset_rfl⟩)

/--
@isnad1 id=eq.0h4v.s5.774974a66f6f from=translated src=- shape=80da9432 vocab=c75f34fd
-/
@[simp] lemma thickening_comp : thickening v (thickening u s) = thickening (u ○ v) s := by
  ext; simp [thickening, ball]

/--
@isnad1 id=iff.0h4v.s6.0166f486ae70 from=translated src=- shape=634a281b vocab=1c856ab9
-/
lemma disjoint_ball_iff : Disjoint (ball a u) t ↔ ∀ b ∈ t, (a, b) ∉ u := by
  rw [← compl_compl (ball a u), disjoint_compl_left_iff_subset]
  rfl

/--
@isnad1 id=iff.0h4v.s6.f7a23dd488c4 from=translated src=- shape=a3ec68cc vocab=b066426e
-/
lemma thickening_inter_eq_empty : thickening u s ∩ t = ∅ ↔ ∀ a ∈ s, ∀ b ∈ t, (a, b) ∉ u := by
  simp [thickening, ← disjoint_iff_inter_eq_empty, disjoint_ball_iff]

/--
@isnad1 id=iff.1h4v.s5.b02bbb2c80ee from=translated src=- shape=36ab4488 vocab=37f153ea
-/
lemma thickening_inter_eq_empty_comm (hu : SetRel.IsSymm u) :
    thickening u s ∩ t = ∅ ↔ s ∩ thickening u t = ∅ := by
  rw [inter_comm s, thickening_inter_eq_empty, thickening_inter_eq_empty]
  constructor <;> exact fun h a ha b hb hab => h b hb a ha (SetRel.symm u hab)

/--
@isnad1 id=eq.3h5v.s6.c81362a2518d from=translated src=- shape=3d9b0979 vocab=cb2f6184
-/
lemma thickening_inter_thickening_eq_empty_of_comp (hv : SetRel.IsSymm v) (hvu : v ○ v ⊆ u)
    (hST : thickening u s ∩ t = ∅) :
    thickening v s ∩ thickening v t = ∅ := by
  simp only [←thickening_inter_eq_empty_comm hv, thickening_comp]
  exact subset_eq_empty (inter_subset_inter_left _ (monotone_thickening hvu)) hST

end UniformSpace

-----------------------------------------------------------------------------

/-- The uniform neighbourhood filter of a set `s`: filter of supersets
of `U`-thickenings of `s` for entourages `U`. Strengthens `𝓝ˢ s` for
locally uniform statements. -/
def uniformNhdsSet [UniformSpace α] (s : Set α) : Filter α :=
  Filter.lift' (𝓤 α) (UniformSpace.thickening · s)

/-- Notation for `uniformNhdsSet`, the uniform neighbourhood filter. -/
scoped[Uniformity] notation "𝓝ᵘ" => uniformNhdsSet

namespace UniformSpace -- uniformNhdsSet

variable [UniformSpace α]

/--
@isnad1 id=mem.1h3v.s5.4ad5cc183d4d from=translated src=- shape=b4a7596b vocab=7f22c10a
-/
lemma thickening_mem_uniform_nhds_set (hu : u ∈ 𝓤 α) : thickening u s ∈ 𝓝ᵘ s :=
  (mem_lift'_sets monotone_thickening).mpr ⟨u, hu, subset_rfl⟩

/--
@isnad1 id=le.1h3v.s5.f350f559e885 from=translated src=- shape=e4a3c269 vocab=de4f6c42
-/
lemma uniform_nhds_set_mono {s t : Set α} (h : s ⊆ t) : 𝓝ᵘ s ≤ 𝓝ᵘ t :=
  lift'_mono le_rfl (fun _ => thickening_mono h)

/--
@isnad1 id=eq.0h2v.s4.517c12e1afb3 from=translated src=- shape=8814e1a4 vocab=6dfeeffa
-/
lemma uniform_nhds_set_singleton {a : α} : 𝓝ᵘ {a} = 𝓝 a := by
  simp only [uniformNhdsSet, thickening_singleton, nhds_eq_uniformity]

/--
@isnad1 id=iff.0h3v.s5.964169490d95 from=translated src=- shape=bee5e59d vocab=3d67fd6e
-/
lemma mem_uniform_nhds_set_iff : s ∈ 𝓝ᵘ t ↔ ∃ u ∈ 𝓤 α, thickening u t ⊆ s := by
  simp [uniformNhdsSet, mem_lift'_sets]

/--
@isnad1 id=le.1h3v.s5.21b5c5bc9c31 from=translated src=- shape=3d0979f7 vocab=4b07eb42
-/
lemma nhds_le_uniform_nhds_set {s : Set α} (ha : a ∈ s) : 𝓝 a ≤ 𝓝ᵘ s := by
  simpa [← uniform_nhds_set_singleton] using uniform_nhds_set_mono (singleton_subset_iff.mpr ha)

/--
@isnad1 id=le.0h2v.s4.7edaaff1002d from=translated src=- shape=a5e9b6d0 vocab=f86004b3
-/
lemma nhds_set_le_uniform_nhds_set {s : Set α} : 𝓝ˢ s ≤ 𝓝ᵘ s := by
  simpa [nhdsSet] using fun _ => nhds_le_uniform_nhds_set

/--
@isnad1 id=eq.1h3v.s5.1417c71a0bd0 from=translated src=- shape=d7e289b3 vocab=838e95b2
-/
lemma uniform_nhds_inf_uniform_nhds_eq_bot {s t : Set α} (h : 𝓝ᵘ s ⊓ 𝓟 t = ⊥) :
    𝓝ᵘ s ⊓ 𝓝ᵘ t = ⊥ := by
  simp_rw [inf_principal_eq_bot, inf_eq_bot_iff, mem_uniform_nhds_set_iff] at h ⊢
  obtain ⟨u, hu, hsu⟩ := h
  obtain ⟨v, hv, hvs, hvu⟩ := comp_symm_of_uniformity hu
  refine ⟨_, ⟨v, hv, subset_rfl⟩, _, ⟨v, hv, subset_rfl⟩, ?h⟩
  apply thickening_inter_thickening_eq_empty_of_comp (symmetricRel_of hvs) hvu
  exact (subset_compl_iff_disjoint_right.mp hsu).inter_eq

/--
@isnad1 id=eq.1h3v.s5.8ce68ba84069 from=translated src=- shape=d3cfe530 vocab=fe4cbb32
-/
lemma nhds_inf_uniform_nhds_eq_bot {s : Set α} (hf : 𝓝 a ⊓ 𝓟 s = ⊥) : 𝓝 a ⊓ 𝓝ᵘ s = ⊥ := by
  rw [← uniform_nhds_set_singleton] at hf ⊢
  exact uniform_nhds_inf_uniform_nhds_eq_bot hf

/--
@isnad1 id=eq.1h2v.s4.a9e340049a8e from=translated src=- shape=ca3a5e82 vocab=194a0d22
-/
lemma nhds_set_eq_uniform_nhds_set_of_isCompact {s : Set α} (hs : IsCompact s) :
    𝓝ˢ s = 𝓝ᵘ s :=
  (hs.nhdsSet_basis_uniformity (basis_sets _)).eq_of_same_basis ⟨fun _ => mem_uniform_nhds_set_iff⟩

end UniformSpace

-----------------------------------------------------------------------------

open UniformSpace

variable {p : Filter ι}

/--
@isnad1 id=tendsto.0h2v.s5.7fadf30ed355 from=translated src=- shape=1e0a8d80 vocab=fa4ca1af
-/
lemma lemma0 [UniformSpace α] : Tendsto Prod.snd (𝓤 α ⊓ comap Prod.fst (𝓟 s)) (𝓝ᵘ s) := by
  simp_rw [comap_principal, uniformNhdsSet, tendsto_lift', eventually_inf_principal]
  exact fun U hU => mem_of_superset hU (fun ⟨x, y⟩ hxy hx => mem_biUnion hx hxy)

/--
@isnad1 id=tendsto.0h6v.s5.54c495335ca7 from=translated src=- shape=8aaef44f vocab=b60da96f
-/
lemma lemma2 {p : Filter ι} {f : α → β} {s : Set α} :
    Tendsto (f ∘ Prod.snd) (p ×ˢ (𝓟 s)) (𝓟 (f '' s)) :=
  (tendsto_principal_principal.mpr <| fun _ => mem_image_of_mem f).comp tendsto_snd

/--
@isnad1 id=tendsto.1h7v.s6.8167a8a2a4a4 from=translated src=- shape=3787751e vocab=02e74c9a
-/
lemma lemma1 {F : ι → α → β} {f : α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (fun (q : ι × α) => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) ((𝓟 (f '' s)) ×ˢ (𝓝ᵘ (f '' s))) := by
  rw [tendstoUniformlyOn_iff_tendsto] at hF
  refine tendsto_prod_iff'.mpr ⟨lemma2, ?h⟩
  exact lemma0.comp (tendsto_inf.mpr ⟨hF, tendsto_comap_iff.mpr lemma2⟩)

/--
@isnad1 id=tendsto.1h7v.s6.a95dc92b3515 from=translated src=- shape=c77b2762 vocab=3342ff1a
-/
lemma lemma13 {f : α → β} {F : ι → α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (uncurry F) (p ×ˢ 𝓟 s) (𝓝ᵘ (f '' s)) :=
  (tendsto_prod_iff'.mp (lemma1 hF)).2
