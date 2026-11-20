import Tengoku.TuzaLean.Tuza.Basic.Packing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite page choices in books. -/

namespace Tuza

namespace Books

open Finset

variable {E I : Type*} [DecidableEq E] [Fintype I]

/-- One page is selected for each index.-/
def ChoosesPages (pages : I → Finset (Finset E)) (f : I → Finset E) : Prop :=
  ∀ i, f i ∈ pages i

/-- The family obtained by choosing one page from each book.-/
def choice (f : I → Finset E) : Finset (Finset E) :=
  Finset.univ.image f

/--
@isnad1 id=iff.0h4v.s5.8c2811298e8f from=translated src=- shape=d7721784 vocab=c3dced98
-/
@[simp] theorem mem_choice {f : I → Finset E} {T : Finset E} :
    T ∈ choice f ↔ ∃ i, f i = T := by
  simp [choice]

/-- Distinct books may share original vertices, but not edges.-/
def DisjointSupports (pages : I → Finset (Finset E)) : Prop :=
  Pairwise (fun i j => Disjoint (support (pages i)) (support (pages j)))

omit [Fintype I] in
/--
@isnad1 id=le.1h5v.s5.0d78f72c5018 from=translated src=- shape=e4f27d0c vocab=e2c69cfb
-/
theorem page_subset_support {pages : I → Finset (Finset E)} {i : I}
    {T : Finset E} (hT : T ∈ pages i) : T ⊆ support (pages i) := by
  intro e he
  exact mem_support.mpr ⟨T, hT, he⟩

omit [DecidableEq E] [Fintype I] in
/--
@isnad1 id=ex.1h3v.s5.8071e082e8d3 from=translated src=- shape=e30c9cd4 vocab=d42ac2cc
-/
theorem exists_choice {pages : I → Finset (Finset E)}
    (hne : ∀ i, (pages i).Nonempty) :
    ∃ f, ChoosesPages pages f := by
  classical
  choose f hf using hne
  exact ⟨f, hf⟩

omit [Fintype I] in
/--
@isnad1 id=pairwise.2h4v.s5.92a414802651 from=translated src=- shape=95965443 vocab=714f6bba
-/
theorem choices_pairwise_disjoint {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Pairwise (fun i j => Disjoint (f i) (f j)) := by
  intro i j hij
  exact (hd hij).mono (page_subset_support (hf i)) (page_subset_support (hf j))

omit [Fintype I] in
/-- Nonempty pages in different books cannot become the same chosen page.
@isnad1 id=injectiv.3h4v.s6.65756c1f1d9d from=translated src=- shape=339f9757 vocab=e2cef780
-/
theorem choice_injective {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Function.Injective f := by
  intro i j hij
  by_contra hneij
  have hdis := choices_pairwise_disjoint hd hf hneij
  obtain ⟨e, he⟩ := hne i (f i) (hf i)
  exact Finset.disjoint_left.mp hdis he (hij ▸ he)

/--
@isnad1 id=eq.3h4v.s6.34d61a2455db from=translated src=- shape=7211c728 vocab=e0729ecd
-/
theorem card_choice {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : (choice f).card = Fintype.card I := by
  rw [choice, Finset.card_image_of_injective _ (choice_injective hd hne hf)]
  exact Finset.card_univ

/-- Every page choice is a packing when all pages belong to the family and
the supports of distinct books are disjoint.
@isnad1 id=ispackin.3h5v.s6.23abbf995767 from=translated src=- shape=428c38bc vocab=9e305e8b
-/
theorem choice_isPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsPacking F (choice f) := by
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    exact hF i (hf i)
  · intro T hT U hU hTU
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    obtain ⟨j, rfl⟩ := mem_choice.mp hU
    apply choices_pairwise_disjoint hd hf
    intro hij
    exact hTU (congrArg f hij)

/-- A known upper bound on every packing makes all full page choices maximum.
@isnad1 id=ismaximu.5h5v.s6.42094da506ab from=translated src=- shape=f01278b9 vocab=2575738e
-/
theorem choice_isMaximumPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty)
    (hbound : ∀ P, IsPacking F P → P.card ≤ Fintype.card I)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsMaximumPacking F (choice f) := by
  refine ⟨choice_isPacking hF hd hf, ?_⟩
  intro P hP
  rw [card_choice hd hne hf]
  exact hbound P hP

/-- Every page choice meets each member of the family.-/
def EveryChoiceMeets (F : Finset (Finset E))
    (pages : I → Finset (Finset E)) : Prop :=
  ∀ f, ChoosesPages pages f → ∀ T ∈ F, ∃ i, ¬ Disjoint T (f i)

/-- Maximum page choices give the required maximality when family members
are nonempty.
@isnad1 id=everycho.2h4v.s6.9a0d46cc8b4d from=translated src=- shape=e0ebf9e9 vocab=8c691add
-/
theorem everyChoiceMeets_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f)) :
    EveryChoiceMeets F pages := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (hmax f hf).meets_support hT (hne T hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (Finset.mem_inter.mp he).2
  obtain ⟨i, rfl⟩ := mem_choice.mp hU
  refine ⟨i, ?_⟩
  intro hdis
  exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp he).1 heU

/-- If every full page choice meets a family member, one book has all its
pages meeting that member.
@isnad1 id=ex.2h5v.s6.56907ec9e38d from=translated src=- shape=d854f17e vocab=378e9200
-/
theorem exists_book_all_pages_meet {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)} (hchoice : EveryChoiceMeets F pages)
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U := by
  classical
  by_contra hnone
  push Not at hnone
  choose f hf hdis using hnone
  obtain ⟨i, hi⟩ := hchoice f hf T hT
  exact hi (hdis i)

/--
@isnad1 id=ex.3h5v.s6.4af81ad3d695 from=translated src=- shape=72abd622 vocab=4d85c5ea
-/
theorem exists_book_all_pages_meet_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f))
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U :=
  exists_book_all_pages_meet (everyChoiceMeets_of_maximum hne hmax) hT

end Books

end Tuza
