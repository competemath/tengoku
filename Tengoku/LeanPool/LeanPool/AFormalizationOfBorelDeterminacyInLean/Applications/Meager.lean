/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.General
import Tengoku.LeanPool.LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.RegularOpen

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.Meager

Auxiliary declarations for the Borel determinacy formalization.
-/

@[expose] public section

variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  (f : X → Y) {A B U V : Set X}
open Topology
/-- Auxiliary declaration for the Borel determinacy formalization. -/
scoped[Topology] notation (name := DenseOf) "Dense[" t "]" => @Dense _ t
/--
@isnad1 id=dense.2h3v.s6.4069ff3dc600 from=translated src=- shape=b876168e vocab=8d7538e5
-/
lemma dense_trans {B : Set A} (hA : Dense A) (hB : Dense B) :
  Dense (Subtype.val '' B) := (Dense.isDenseEmbedding_val hA).dense_image.mpr hB
open Set.Notation
/--
@isnad1 id=dense.0h2v.s5.2b69c79f923a from=translated src=- shape=b070e629 vocab=499fad5d
-/
lemma dense_in_closure (A : Set X) : Dense (closure A ↓∩ A) := by
  rw [Subtype.dense_iff]
  apply closure_mono
  simp [subset_closure]

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def openDenseFilterBasis : FilterBasis X where
  sets := {U | IsOpen U ∧ Dense U}
  nonempty := ⟨Set.univ, ⟨isOpen_univ, dense_univ⟩⟩
  inter_sets {U V} hU hV := ⟨U ∩ V,
    ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen_left hV.2 hU.1⟩, subset_rfl⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev openDenseFilter : Filter X := openDenseFilterBasis.filter

/--
@isnad1 id=isnowher.1h3v.s4.253195bf33d2 from=translated src=- shape=a0ad1a89 vocab=8f8374e0
-/
lemma IsNowhereDense.inter_left (hA : IsNowhereDense A) :
  IsNowhereDense (A ∩ B) := hA.mono Set.inter_subset_left
/--
@isnad1 id=isnowher.1h3v.s4.4455810d7861 from=translated src=- shape=27d5fd07 vocab=8f8374e0
-/
lemma IsNowhereDense.inter_right (hA : IsNowhereDense A) :
  IsNowhereDense (B ∩ A) := hA.mono Set.inter_subset_right
/--
@isnad1 id=iff.0h2v.s5.b517f3b18aa7 from=translated src=- shape=d6d27087 vocab=14cf4c3d
-/
lemma isNowhereDense_iff_subset_closed_nowhereDense :
  IsNowhereDense A ↔ ∃ C, A ⊆ C ∧ IsClosed C ∧ IsNowhereDense C where
  mp := by
    -- Mathlib should handle the conjunct order uniformly here.
    simpa [and_comm] using IsNowhereDense.subset_of_closed_isNowhereDense
  mpr := fun ⟨_, hS, _, hN⟩ ↦ hN.mono hS
/--
@isnad1 id=iff.0h2v.s4.94795ef837cf from=translated src=- shape=f269b021 vocab=6522495b
-/
lemma isNowhereDense_iff_compl_contains_openDense :
  IsNowhereDense A ↔ Aᶜ ∈ openDenseFilter := by
  rw [isNowhereDense_iff_subset_closed_nowhereDense, compl_surjective.exists]
  simp_rw [isClosed_isNowhereDense_iff_compl,
    FilterBasis.mem_filter_iff, ← FilterBasis.mem_sets, openDenseFilterBasis]
  simp [and_comm, Set.subset_compl_comm]
/--
@isnad1 id=isnowher.2h3v.s4.91fb69be70e0 from=translated src=- shape=0540dca0 vocab=ddc15c7e
-/
lemma isNowhereDense.union (hA : IsNowhereDense A) (hB : IsNowhereDense B) :
  IsNowhereDense (A ∪ B) := by
  simpa [isNowhereDense_iff_compl_contains_openDense] using And.intro hA hB
/--
@isnad1 id=isnowher.1h3v.s5.af9d93b31bf7 from=translated src=- shape=ff438511 vocab=b50a4d84
-/
lemma isNowhereDense_iUnion {I} {A : I → Set X} [Finite I] (h : ∀ i, IsNowhereDense (A i)) :
  IsNowhereDense (⋃ i, A i) := by
  simpa [isNowhereDense_iff_compl_contains_openDense] using h
/--
@isnad1 id=tendsto.2h3v.s5.e9363c0001a2 from=translated src=- shape=2d2c8bec vocab=ca087782
-/
lemma tendsto_openDense_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) :
  Filter.Tendsto f openDenseFilter openDenseFilter :=
  openDenseFilterBasis.hasBasis.ge_iff.mpr fun U ⟨hUo, hUd⟩ ↦
    ⟨f⁻¹' U, ⟨hUo.preimage hc, hUd.preimage ho⟩, subset_rfl⟩
/--
@isnad1 id=isnowher.3h4v.s5.5d699747cce9 from=translated src=- shape=91a05794 vocab=afb6a2e4
-/
lemma IsNowhereDense.preimage {A : Set Y} (h : IsNowhereDense A)
  (hc : Continuous f) (ho : IsOpenMap f) : IsNowhereDense (f⁻¹' A) := by
  rw [isNowhereDense_iff_compl_contains_openDense] at h ⊢
  simpa [Set.preimage_compl] using tendsto_openDense_of_isOpenMap f hc ho h

/--
@isnad1 id=dense.2h3v.s5.961101e77c8f from=translated src=- shape=d2f73d53 vocab=22bf70ff
-/
lemma Dense.dense_in_open (hU : IsOpen U) (hD : Dense A) : Dense (U ↓∩ A) :=
  hD.preimage hU.isOpenMap_subtype_val
/--
@isnad1 id=iff.0h2v.s6.58781daeecea from=translated src=- shape=09ade63a vocab=6e20d00f
-/
lemma somewhereDense_iff : ¬ IsNowhereDense A ↔ ∃ U, U.Nonempty ∧ IsOpen U ∧ Dense (U ↓∩ A) := by
  simp_rw [Subtype.dense_iff, Subtype.image_preimage_coe]; constructor
  · intro h
    use interior (closure A), Set.notMem_singleton_empty.mp h, isOpen_interior
    apply subset_trans _ isOpen_interior.inter_closure; simp [Eq.subset, interior_subset]
  · intro ⟨U, hUd, hUo, hUs⟩; simp_rw [IsNowhereDense, ← Set.nonempty_iff_ne_empty]
    use hUd.choose; rw [mem_interior]
    use U, subset_trans hUs (closure_mono Set.inter_subset_right), hUo, hUd.choose_spec
/--
@isnad1 id=iff.0h2v.s5.9791c472b129 from=translated src=- shape=af21546e vocab=6e20d00f
-/
lemma nowhereDense_iff : IsNowhereDense A ↔ ∀ U, U.Nonempty → IsOpen U → ¬ Dense (U ↓∩ A) := by
  simpa using not_iff_not.mpr somewhereDense_iff

/--
@isnad1 id=isnowher.2h4v.s5.3866baff2902 from=translated src=- shape=b97bd5f5 vocab=d6de2c23
-/
lemma isNowhereDense_image (hf : IsInducing f) (h : IsNowhereDense A) :
  IsNowhereDense (f '' A) := by
  simp_rw [IsNowhereDense, hf.closure_eq_preimage_closure_image] at *
  replace h := subset_trans (preimage_interior_subset_interior_preimage hf.continuous) h.subset
  rw [Set.subset_empty_iff, Set.preimage_eq_empty_iff] at h
  simpa using Set.disjoint_of_subset_right
    (subset_trans (interior_mono (closure_mono (Set.image_subset_range f A))) interior_subset)
    (Disjoint.closure_right h isOpen_interior)

/--
@isnad1 id=iff.1h3v.s6.4dfdf5dd5ce4 from=translated src=- shape=856fb250 vocab=0d3c2670
-/
lemma nowhereDense_in_open (hU : IsOpen U) (A : Set U) :
  IsNowhereDense (Subtype.val '' A) ↔ IsNowhereDense A := by
  constructor <;> intro h
  · simpa using h.preimage (f := Subtype.val) continuous_subtype_val hU.isOpenMap_subtype_val
  · exact isNowhereDense_image _ IsInducing.subtypeVal h
/--
@isnad1 id=iff.1h3v.s6.42090ef3dca3 from=translated src=- shape=856fb250 vocab=ffdeb061
-/
lemma nowhereDense_in_dense (hU : Dense U) (A : Set U) :
  IsNowhereDense (Subtype.val '' A) ↔ IsNowhereDense A := by
  constructor
  · intro h
    simp_rw [isNowhereDense_iff_compl_contains_openDense, FilterBasis.mem_filter_iff] at *
    obtain ⟨V, ⟨hVo, hVd⟩, hVs⟩ := h
    use U ↓∩ V
    constructor
    · use hVo.preimage continuous_subtype_val
      rw [← hU.isDenseEmbedding_val.dense_image]
      simpa using Dense.inter_of_isOpen_right hU hVd hVo
    · simpa [Set.subset_compl_iff_disjoint_left, projection_formula] using hVs
  · intro h
    exact isNowhereDense_image _ IsInducing.subtypeVal h
/--
@isnad1 id=iff.1h2v.s4.3aa2e2263a7e from=translated src=- shape=cd5270fa vocab=d5894bae
-/
lemma isOpen_isNowhereDense (hU : IsOpen U) : IsNowhereDense U ↔ U = ∅ := by
  rw [← Subtype.coe_image_univ U, nowhereDense_in_open hU Set.univ]
  simp [IsNowhereDense]
/--
@isnad1 id=not.1h2v.s4.ec697a8edfdc from=translated src=- shape=a8076495 vocab=ad1303bd
-/
lemma Dense.somewhereDense [Nonempty X] (hU : Dense U) : ¬ IsNowhereDense U := by
  simp [IsNowhereDense, hU.closure_eq]
/--
@isnad1 id=nonempty.1h2v.s4.3ef48c058cbc from=translated src=- shape=2fb328a6 vocab=fdf9d927
-/
lemma nonempty_of_somewhereDense (h : ¬ IsNowhereDense A) : Nonempty A := by
  by_contra hc; have heq : A = ∅ := Set.isEmpty_coe_sort.mp ⟨fun a ↦ hc ⟨a⟩⟩
  subst heq; exact h isNowhereDense_empty

/--
@isnad1 id=ex.1h4v.s6.fadde5792c49 from=translated src=- shape=447d3b13 vocab=d8573621
-/
lemma fiber_somewhereDense (h : ¬ IsNowhereDense U) {α} (f : U → α) [Finite α] :
    ∃ a, ¬ IsNowhereDense (Subtype.val '' (f⁻¹' {a})) := by
  by_contra hA; push Not at hA; apply h
  simpa [← Set.image_iUnion, ← Set.preimage_iUnion, Set.iUnion_of_singleton]
    using isNowhereDense_iUnion hA

/--
@isnad1 id=eq.2h4v.s5.0a969c16fe83 from=translated src=- shape=ffcdd9c4 vocab=ba6da511
-/
lemma closure_open_cover {I} (U : I → Set X) (hO : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    closure A = ⋃ i, closure (A ∩ U i) := by
  apply subset_antisymm _ (by simp [closure_mono])
  intro x hx
  simp_rw [Set.mem_iUnion, mem_closure_iff] at *
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by simp_rw [← Set.mem_iUnion, hcov, Set.mem_univ]
  use i; intro V hV hxV
  convert hx (V ∩ U i) (hV.inter (hO i)) ⟨hxV, hi⟩ using 1
  tauto_set
/--
@isnad1 id=eq.2h4v.s5.eb04d183a8a8 from=translated src=- shape=ffcdd9c4 vocab=e445d5e7
-/
lemma interior_open_cover {I} (U : I → Set X) (hO : ∀ i, IsOpen (U i))
  (hcov : ⋃ i, U i = Set.univ) :
    interior A = ⋃ i, interior (A ∩ U i) := by
  apply subset_antisymm _ (by simp)
  intro x hx
  simp_rw [Set.mem_iUnion, mem_interior] at *
  obtain ⟨V, hVA, hVo, hVx⟩ := hx
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by simp_rw [← Set.mem_iUnion, hcov, Set.mem_univ]
  use i, V ∩ U i, by tauto_set, (hVo.inter (hO i)), by tauto_set
/--
@isnad1 id=isclosed.3h4v.s6.6a8246dd2e4b from=translated src=- shape=4b873170 vocab=3c640920
-/
lemma open_cover_closed {I} (U : I → Set X) (hO : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
  (hd : Pairwise (Function.onFun Disjoint U)) i :
    IsClosed (U i) := by
  rw [← isOpen_compl_iff, Set.compl_eq_univ_sdiff, ← hcov, Set.iUnion_sdiff]
  apply isOpen_iUnion; intro j
  by_cases h : i = j
  · simp [h]
  · rw [(hd h).sdiff_eq_right]; apply hO
/--
@isnad1 id=eq.1h3v.s5.b8818d4810c7 from=translated src=- shape=4499a3f1 vocab=d97002a4
-/
lemma IsClopen.inter_closure (h : IsClopen U) {A} : closure A ∩ U = closure (A ∩ U) := by
  apply subset_antisymm h.isOpen.closure_inter
  nth_rw 2 [← h.isClosed.closure_eq]; simp [closure_mono]
/--
@isnad1 id=iff.2h3v.s6.876d3392f767 from=translated src=- shape=43d378fd vocab=4302de4e
-/
lemma nowhereDense_iff_nowhereDense_in_open (hU : IsOpen U) (hA : A ⊆ U) :
  IsNowhereDense A ↔ IsNowhereDense (U ↓∩ A) := by
  rw [← nowhereDense_in_open hU, Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right hA]
/--
@isnad1 id=isnowher.4h4v.s6.bae80b1d1384 from=translated src=- shape=5d48de7c vocab=4a8e5d41
-/
lemma isNowhereDense_disjoint_open {I} (U : I → Set X) (hO : ∀ i, IsOpen (U i))
  (hcov : A ⊆ ⋃ i, U i) (hd : Pairwise (Function.onFun Disjoint U))
  (h : ∀ i, IsNowhereDense (A ∩ U i)) : IsNowhereDense (A) := by
  let V := ⋃ i, U i
  have hvO : IsOpen V := isOpen_iUnion hO
  rw [nowhereDense_iff_nowhereDense_in_open hvO hcov]
  replace h := fun i ↦ (nowhereDense_iff_nowhereDense_in_open hvO (by tauto_set)).mp (h i)
  simp_rw [Set.preimage_inter] at h
  have hO' i : IsOpen (V ↓∩ U i) := (hO i).preimage continuous_subtype_val
  have hcov : ⋃ i, V ↓∩ U i = Set.univ := by aesop
  have hC := open_cover_closed _ hO' hcov fun _ _ ij ↦ (hd ij).preimage _
  have hCl i : IsClopen (V ↓∩ U i) := ⟨hC i, hO' i⟩
  unfold IsNowhereDense at *
  rw [interior_open_cover _ hO' hcov, closure_open_cover _ hO' hcov]
  have heq i B : closure B ∩ V ↓∩ U i = closure (B ∩ V ↓∩ U i) :=
    (hCl i).inter_closure
  simp_rw [Set.iUnion_inter, heq, Set.inter_assoc,
    ← fun i j ↦ ((hCl j).inter (hCl i)).inter_closure (A := V ↓∩ A),
    ← Set.inter_iUnion, ← Set.iUnion_inter, hcov, Set.univ_inter, heq, Set.iUnion_eq_empty]
  exact h

/--
@isnad1 id=le.0h1v.s4.e24fe1b50716 from=translated src=- shape=e716c754 vocab=e25c7702
-/
lemma residual_le_openDense : residual X ≤ openDenseFilter := by
  unfold openDenseFilter
  rw [openDenseFilterBasis.hasBasis.ge_iff]
  exact fun _ h ↦ residual_of_dense_open h.1 h.2
/--
@isnad1 id=iff.0h2v.s5.58948cd7858e from=translated src=- shape=c71547e4 vocab=996ba542
-/
lemma isMeagre_iff_eq_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s = ⋃₀ S := by
  rw [isMeagre_iff_countable_union_isNowhereDense]; constructor
  · intro ⟨S, h1, h2, h3⟩
    use (fun x ↦ x ∩ s) '' S
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Set.sUnion_image]
    use fun s h ↦ (h1 s h).inter_left, h2.image _
    exact subset_antisymm (by simpa [← Set.iUnion₂_inter, ← Set.sUnion_eq_biUnion]) (by simp)
  · rintro ⟨S, h1, h2, rfl⟩
    exact ⟨S, h1, h2, subset_rfl⟩
lemma IsMeagre.eq_countable_union_isNowhereDense (h : IsMeagre A) :
  ∃ f : ℕ → {t : Set X | IsNowhereDense t}, A = ⋃ n, f n := by
  rw [isMeagre_iff_eq_countable_union_isNowhereDense] at h
  obtain ⟨S, h1, h2, rfl⟩ := h
  by_cases hS : S.Nonempty
  · rw [Set.countable_iff_exists_surjective hS] at h2
    obtain ⟨f, h2⟩ := h2
    use fun n ↦ ⟨f n, h1 _ (f n).2⟩
    rw [h2.iUnion_comp (fun x ↦ x.1)]
    simp_rw [Set.iUnion_coe_set, Set.sUnion_eq_biUnion]
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    subst hS; use fun f ↦ ⟨∅, isNowhereDense_empty⟩; simp

/--
@isnad1 id=eq.1h2v.s4.35771da9a536 from=translated src=- shape=4c7b0db4 vocab=a92f791a
-/
lemma IsMeagre.interior [BaireSpace X] {U : Set X} (hU : IsMeagre U) : interior U = ∅ := by
  apply compl_injective
  simpa only [Set.compl_empty, ← closure_compl, ← dense_iff_closure_eq]
    using dense_of_mem_residual hU
/--
@isnad1 id=ismeagre.2h4v.s5.e9a2ce739d30 from=translated src=- shape=b97bd5f5 vocab=87ad7afc
-/
lemma isMeagre_image (hf : IsInducing f) (h : IsMeagre A) : IsMeagre (f '' A) := by
  rw [isMeagre_iff_eq_countable_union_isNowhereDense] at *
  obtain ⟨S, h1, h2, h3⟩ := h
  use (fun s ↦ f '' s) '' S
  constructor
  · rintro _ ⟨x, hx, rfl⟩; exact isNowhereDense_image _ hf (h1 x hx)
  · use h2.image _
    simp [h3, Set.sUnion_eq_biUnion, Set.image_iUnion]

/--
@isnad1 id=iff.0h1v.s4.5290b9d731ad from=translated src=- shape=70479290 vocab=a92f791a
-/
lemma baireSpace_iff_isMeagre_interior : BaireSpace X ↔
  ∀ U : Set X, IsMeagre U → interior U = ∅ := by
  use @IsMeagre.interior _ _
  intro h; constructor
  intro f hO hD
  simp_rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, Set.compl_iInter,
    Set.compl_univ_iff]
  apply h; apply isMeagre_iUnion; intro n
  simpa [IsMeagre] using residual_of_dense_open (hO n) (hD n)
/--
@isnad1 id=iff.1h2v.s4.10a235b246d1 from=translated src=- shape=bdb43d30 vocab=3a9911f2
-/
lemma isOpen_isMeagre [BaireSpace X] {U : Set X} (hU : IsOpen U) : IsMeagre U ↔ U = ∅ :=
  ⟨by intro h; rwa [← h.interior, Eq.comm, interior_eq_iff_isOpen],
    by rintro rfl; exact IsMeagre.empty⟩
/--
@isnad1 id=iff.0h1v.s4.c7051467ebaf from=translated src=- shape=ed0fe8ac vocab=3a9911f2
-/
lemma baireSpace_iff_isMeagre_isOpen : BaireSpace X ↔
  ∀ U : Set X, IsMeagre U → IsOpen U → U = ∅ := by
  constructor
  · have := @isOpen_isMeagre (X := X); aesop
  · simp_rw [baireSpace_iff_isMeagre_interior]
    exact fun h U hU ↦ h _ (hU.mono interior_subset) isOpen_interior
/--
@isnad1 id=bairespa.1h2v.s5.894684bbd111 from=translated src=- shape=bccbd022 vocab=9ffc2d8a
-/
lemma open_baire [BaireSpace X] {U : Set X} (hU : IsOpen U) : BaireSpace U := by
  rw [baireSpace_iff_isMeagre_isOpen]
  intro V hVm hVo
  rw [← Set.image_eq_empty (f := Subtype.val), ← isOpen_isMeagre]
  · exact isMeagre_image _ IsInducing.subtypeVal hVm
  · exact IsOpen.trans hVo hU

namespace residual.dom
variable {U V : tX.Opens}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Forces (U : tX.Opens) (A : Set X) : Prop :=
  ((U : Set X) ↓∩ A) ∈ residual (U : Set X)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
scoped notation:50 U " ⊩ " A:50 =>
  Forces U A
/--
@isnad1 id=iff.0h3v.s5.a901b7b72f83 from=translated src=- shape=703189ba vocab=0c93084e
-/
lemma forces_iff_isMeagre : U ⊩ A ↔ IsMeagre (U \ A) := by
  change ((U : Set X) ↓∩ A ∈ residual (U : Set X)) ↔ IsMeagre (U \ A)
  constructor <;> intro h
  · rw [← compl_compl ((U : Set X) ↓∩ A)] at h
    convert isMeagre_image Subtype.val IsInducing.subtypeVal h
    conv => simp [← Set.preimage_compl, Set.image_preimage_eq_inter_range]
    tauto_set
  · simpa [IsMeagre, - SetLike.coe_sort_coe, Set.compl_eq_univ_sdiff] using
      h.preimage_of_isOpenMap continuous_subtype_val U.isOpen.isOpenMap_subtype_val
/--
@isnad1 id=iff.0h2v.s4.7c24d82040cd from=translated src=- shape=494e0705 vocab=c2fbaff4
-/
lemma forces_empty_iff_isMeagre : U ⊩ ∅ ↔ IsMeagre (U : Set X) := by
  simpa using forces_iff_isMeagre (A := ∅)
/--
@isnad1 id=forces.2h4v.s5.3bc0769a2151 from=translated src=- shape=fb04da86 vocab=343c2884
-/
lemma forces_mono_left (h : V ⊩ A) (hUV : U.1 ⊆ V.1) : U ⊩ A := by
  rw [forces_iff_isMeagre] at *
  exact h.mono (by tauto_set)
/--
@isnad1 id=forces.2h4v.s5.b6899305f5ac from=translated src=- shape=01dfef94 vocab=e9274f30
-/
lemma forces_mono_right (h : U ⊩ A) (hAB : A ⊆ B) : U ⊩ B :=
  Filter.mem_of_superset h (by tauto_set)
/--
@isnad1 id=forces.1h4v.s5.b8038e88ffeb from=translated src=- shape=559a4382 vocab=d83b10c2
-/
lemma forces_iInter_right {I} [Countable I] (A : I → Set X)
  (h : ∀ i, U ⊩ A i) : U ⊩ ⋂ i, A i := by
  change ((U : Set X) ↓∩ ⋂ i, A i ∈ residual (U : Set X))
  simpa [Forces, Set.preimage_iInter] using countable_iInter_mem.mpr h
/--
@isnad1 id=forces.0h2v.s4.06a0b8f78453 from=translated src=- shape=3dfbfa29 vocab=ad2681bf
-/
lemma forces_rfl : U ⊩ U := by rw [forces_iff_isMeagre]; simp [IsMeagre.empty]
/--
@isnad1 id=forces.2h4v.s5.426f76412486 from=translated src=- shape=3f6bdc65 vocab=2d87d32b
-/
lemma forces_trans (hU : U ⊩ V) (h : V ⊩ A) : U ⊩ A := by
  rw [forces_iff_isMeagre] at *
  exact (hU.union h).mono diff_subset_union
private lemma forces_disjoint_iUnion_left {I} (U : I → tX.Opens)
  (hd : Pairwise (Function.onFun Disjoint (fun i ↦ (U i : Set X)))) (h : ∀ i, U i ⊩ A) :
  ⨆ i, U i ⊩ A := by
  simp_rw [forces_iff_isMeagre] at *
  let V i := (h i).eq_countable_union_isNowhereDense.choose
  have hV i : (U i : Set X) \ A = ⋃ n, V i n := (h i).eq_countable_union_isNowhereDense.choose_spec
  have hVU i n : (V i n).val ⊆ U i :=
    subset_trans (Set.subset_iUnion_of_subset n subset_rfl) ((hV i).superset.trans Set.sdiff_subset)
  simp_rw [TopologicalSpace.Opens.coe_iSup, Set.iUnion_sdiff, hV]
  rw [Set.iUnion_comm]; apply isMeagre_iUnion
  intro n; apply IsNowhereDense.isMeagre
  apply isNowhereDense_disjoint_open (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen)
    (by rw [Set.iUnion_subset_iff]; intro i; apply Set.subset_iUnion_of_subset; apply hVU) hd
    (fun i ↦ by
      have heq : (⋃ i, (V i n).val) ∩ (U i : Set X) = (V i n).val := by
        apply subset_antisymm _ (by simpa [hVU] using Set.subset_iUnion (fun i ↦ (V i n).val) i)
        intro x ⟨h, hxU⟩
        obtain ⟨j, hj⟩ := by simpa using h
        specialize hd (i := i) (j := j)
        simp [Function.onFun, - TopologicalSpace.Opens.coe_disjoint] at hd
        by_cases i = j <;> tauto_set
      rw [heq]
      exact (V i n).prop)
end residual.dom
open residual.dom in
/-- a Baire category analogue of outer measure -/
def dom (A : Set X) : tX.Opens := ⨆ (U) (_ : U ⊩ A), U
namespace residual.dom
/--
@isnad1 id=forces.0h2v.s4.50f8f84b52b1 from=translated src=- shape=903e385d vocab=624d2cc4
-/
lemma forces : dom A ⊩ A := by
  let S := {C : Set tX.Opens | C.PairwiseDisjoint id ∧ ∀ U ∈ C, U ⊩ A}
  obtain ⟨U, ⟨⟨hdis, hfor⟩, hUmax⟩⟩ := zorn_subset S (fun c hcS hc ↦ ⟨⋃₀ c,
    ⟨(Set.pairwise_sUnion hc.directedOn).mpr (fun U h ↦ (hcS h).1),
    fun U ⟨i, h, h'⟩ ↦ (hcS h).2 _ h'⟩, @Set.subset_sUnion_of_mem _ _⟩)
  have hf1 : dom A ⊩ (⨆ V : U, V : tX.Opens) := by
    apply residual_of_dense_open ((⨆ V : U, V : tX.Opens).isOpen.preimage continuous_subtype_val)
    rw [dense_iff_inter_open]
    intro W' hWo ⟨x, hxW'⟩
    obtain ⟨W'', hW''A, hxW''⟩ := by simpa [dom] using x.prop
    let W := W'' ⊓ ⟨W', hWo.trans (dom A).isOpen⟩
    by_contra habs
    rw [Set.not_nonempty_iff_eq_empty, ← Set.subset_empty_iff, ← Set.disjoint_iff,
      projection_formula] at habs
    specialize hUmax (y := U ∪ {W}) (by
      conv => simp [S]
      refine ⟨?_, forces_mono_left hW''A (by simp [W]), hfor⟩
      rw [← Set.union_singleton, Set.pairwiseDisjoint_union]
      use hdis
      conv at habs => simp
      conv => simp
      intro V hV _
      specialize habs V hV
      convert habs.mono_left (a := (W : Set X)) (by simp [W])
      simp [disjoint_iff, SetLike.ext'_iff, Set.inter_comm]) (by simp)
    rw [Set.union_subset_iff] at hUmax
    conv at hUmax => simp
    replace habs := habs.mono (a := (W : Set X)) (c := (W : Set X)) (by simp [W])
      (le_iSup₂_of_le W (by simpa using hUmax) le_rfl)
    conv at habs => simp
    have : x.val ∈ (W : Set X) := ⟨hxW'', by simpa using hxW'⟩
    rwa [habs] at this
  have hf2 : ⨆ V : U, V ⊩ A := by
    apply forces_disjoint_iUnion_left _ _ (by simpa)
    simp_rw [Set.PairwiseDisjoint, Set.Pairwise, ne_eq] at hdis
    simp_rw [Pairwise, ne_eq, Subtype.forall, Subtype.mk.injEq]
    convert hdis
    simp [Function.onFun, disjoint_iff, SetLike.ext'_iff]
  exact forces_trans hf1 hf2
/--
@isnad1 id=iff.0h3v.s5.8434a552c100 from=translated src=- shape=df09a4b0 vocab=d3373329
-/
lemma forces_iff_le_dom {U : tX.Opens} : U ⊩ A ↔ U ≤ dom A where
  mp h := by
    conv => simp [dom]
    exact Set.subset_iUnion₂_of_subset U h subset_rfl
  mpr h := forces_mono_left forces h
/--
@isnad1 id=iff.0h3v.s5.90804ac46ef0 from=translated src=- shape=e37f2b91 vocab=9d3fe9d7
-/
lemma forces_iff_subset_dom {U : tX.Opens} : U ⊩ A ↔ (U : Set X) ⊆ dom A := forces_iff_le_dom
/--
@isnad1 id=forces.1h4v.s5.2166c7916ffd from=translated src=- shape=39a53feb vocab=88f12eec
-/
lemma forces_iUnion_left {I} (U : I → tX.Opens) (h : ∀ i, U i ⊩ A) : ⨆ i, U i ⊩ A := by
  simp_rw [forces_iff_subset_dom] at *; simpa
/--
@isnad1 id=ismeagre.0h1v.s4.845dd50b5fb6 from=translated src=- shape=78d7c57d vocab=420f2de2
-/
lemma dom_empty_isMeagre : IsMeagre (dom (∅ : Set X) : Set X) := by
  have h := forces (X := X) (A := ∅)
  rw [forces_iff_isMeagre] at h
  simpa using h
/--
@isnad1 id=ismeagre.2h3v.s5.fa3022823a84 from=translated src=- shape=39786ce1 vocab=536f4f24
-/
lemma banach_category {I} (U : I → Set X) (hUo : ∀ i, IsOpen (U i)) (hUm : ∀ i, IsMeagre (U i)) :
  IsMeagre (⋃ i, U i) := by
  suffices IsMeagre ((⨆ i, TopologicalSpace.Opens.mk (U i) (hUo i) : tX.Opens) : Set X) by simpa
  replace hUm : ∀ i, IsMeagre ((TopologicalSpace.Opens.mk (U i) (hUo i) : tX.Opens) : Set X) := hUm
  simp_rw [← forces_empty_iff_isMeagre] at *
  exact forces_iUnion_left _ hUm

end residual.dom
