import Tengoku.TuzaLean.Tuza.Construction.Types
import Tengoku.TuzaLean.Tuza.Books.Families
import Tengoku.TuzaLean.Tuza.Books.Cover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The first book cover uses a maximum packing and a packing of type-1 triangles.
A two-for-one exchange shows that distinct type-1 pages have distinct parents.
-/

namespace Tuza
namespace FirstCover

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Finset (Sym2 V)} {P Q : Finset (Finset (Sym2 V))}

def children (P Q : Finset (Finset (Sym2 V))) (p : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := Q.filter (fun q => q ∩ support P ⊆ p)

def pages (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    Finset (Finset (Sym2 V)) := insert p.val (children P Q p.val)

omit [Fintype V] in
/--
@isnad1 id=iff.0h5v.s6.5ffac19b4ad4 from=translated src=- shape=d5805ac4 vocab=bc308d14
-/
@[simp] theorem mem_children {p q : Finset (Sym2 V)} :
    q ∈ children P Q p ↔ q ∈ Q ∧ q ∩ support P ⊆ p := by
  simp [children]

omit [Fintype V] in
/--
@isnad1 id=iff.0h5v.s7.cd74281e2ffc from=translated src=- shape=dc1ad113 vocab=7c48f720
-/
@[simp] theorem mem_pages {p : {T // T ∈ P}} {T : Finset (Sym2 V)} :
    T ∈ pages P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ support P ⊆ p.val) := by
  simp [pages]

/--
@isnad1 id=nonempty.2h5v.s6.41a961cf8344 from=translated src=- shape=3bd532c5 vocab=32f5f18f
-/
theorem old_inter_nonempty (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : (q ∩ support P).Nonempty := by
  apply card_pos.mp
  rw [(mem_typeFamily.mp (hQ.1 hq)).2]
  decide

/--
@isnad1 id=ex.1h5v.s7.441b92cf4786 from=translated src=- shape=3a590c65 vocab=2d1eee83
-/
theorem exists_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : ∃ p : {T // T ∈ P}, q.val ∩ support P ⊆ p.val := by
  obtain ⟨e, heq⟩ := card_eq_one.mp (mem_typeFamily.mp (hQ.1 q.property)).2
  have he : e ∈ q.val ∩ support P := by rw [heq]; simp
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_inter.mp he).2
  refine ⟨⟨p, hp⟩, ?_⟩
  rw [heq]
  exact singleton_subset_iff.mpr hep

noncomputable def parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : {T // T ∈ P} := Classical.choose (exists_parent hQ q)

/--
@isnad1 id=le.1h5v.s7.fcefbf56e62f from=translated src=- shape=09adc7f1 vocab=a035ff45
-/
theorem parent_spec (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : q.val ∩ support P ⊆ (parent hQ q).val :=
  Classical.choose_spec (exists_parent hQ q)

/--
@isnad1 id=eq.5h7v.s8.e0e983250d0d from=translated src=- shape=17123cb3 vocab=6d924a63
-/
theorem owner_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) {q : Finset (Sym2 V)}
    (hq : q ∈ Q) (p p' : {T // T ∈ P})
    (hp : q ∩ support P ⊆ p.val) (hp' : q ∩ support P ⊆ p'.val) : p = p' := by
  by_contra hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  obtain ⟨e, he⟩ := old_inter_nonempty hQ hq
  exact disjoint_left.mp (hP.2 p.property p'.property hval) (hp he) (hp' he)

/--
@isnad1 id=eq.3h6v.s8.676a6b8e640b from=translated src=- shape=e132a903 vocab=936a448b
-/
theorem parent_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (hp : q.val ∩ support P ⊆ p.val) : p = parent hQ q :=
  owner_unique hP hQ q.property p (parent hQ q) hp (parent_spec hQ q)

/--
@isnad1 id=injectiv.2h4v.s7.a032dd957edb from=translated src=- shape=ed27ac59 vocab=787b1c3c
-/
theorem parent_injective (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Function.Injective (parent hQ) := by
  intro q q' heq
  by_contra hne
  have hval : q.val ≠ q'.val := fun h => hne (Subtype.ext h)
  have hqt := (mem_typeFamily.mp (hQ.1 q.property)).1
  have hq't := (mem_typeFamily.mp (hQ.1 q'.property)).1
  have havoid : Disjoint q.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq heP
    exact parent_spec hQ q (mem_inter.mpr ⟨heq, heP⟩)
  have havoid' : Disjoint q'.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq' heP
    have h := parent_spec hQ q' (mem_inter.mpr ⟨heq', heP⟩)
    simpa only [← heq] using h
  exact hP.no_two_for_one (parent hQ q).property hqt hq't
    (trianglesOn_nonempty hqt) (trianglesOn_nonempty hq't)
    (hQ.2 q.property q'.property hval) havoid havoid'

/--
@isnad1 id=not.2h5v.s6.caa9a0779366 from=translated src=- shape=438f6233 vocab=1cbaf816
-/
theorem child_not_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : q ∉ P := by
  intro hp
  have heq : q ∩ support P = q := by
    apply inter_eq_left.mpr
    intro e he
    exact mem_support.mpr ⟨q, hp, he⟩
  have hc := (mem_typeFamily.mp (hQ.1 hq)).2
  have ht := trianglesOn_card (mem_typeFamily.mp (hQ.1 hq)).1
  rw [heq] at hc
  omega

/--
@isnad1 id=le.2h5v.s7.e9eeb317b581 from=translated src=- shape=1e14a92e vocab=83f5bdb9
-/
theorem children_card_le_one (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (children P Q p.val).card ≤ 1 := by
  apply card_le_one.mpr
  intro q hq q' hq'
  obtain ⟨hqQ, hqp⟩ := mem_children.mp hq
  obtain ⟨hq'Q, hq'p⟩ := mem_children.mp hq'
  have h₁ := parent_unique hP.1 hQ ⟨q, hqQ⟩ p hqp
  have h₂ := parent_unique hP.1 hQ ⟨q', hq'Q⟩ p hq'p
  exact congrArg Subtype.val (parent_injective hP hQ (h₁.symm.trans h₂))

/--
@isnad1 id=not.1h5v.s7.1682264e4f4d from=translated src=- shape=bfab231d vocab=2f429779
-/
theorem parent_not_child (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : p.val ∉ children P Q p.val := by
  intro hp
  exact child_not_parent hQ (mem_children.mp hp).1 p.property

omit [Fintype V] in
/--
@isnad1 id=nonempty.0h4v.s5.fc3ba1f4d7a4 from=translated src=- shape=61deb88b vocab=1b871537
-/
theorem pages_nonempty (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    (pages P Q p).Nonempty := ⟨p.val, mem_insert_self _ _⟩

/--
@isnad1 id=le.2h5v.s6.4a9058df13f3 from=translated src=- shape=c1446051 vocab=f063045f
-/
theorem pages_subset_family (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    pages P Q p ⊆ trianglesOn A := by
  intro T hT
  rcases mem_pages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1 p.property
  · exact (mem_typeFamily.mp (hQ.1 hTQ)).1

/--
@isnad1 id=le.2h5v.s6.3bf9f54a540a from=translated src=- shape=0065a8f4 vocab=7c4be817
-/
theorem pages_card_le_two (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (pages P Q p).card ≤ 2 := by
  have hle := children_card_le_one hP hQ p
  rw [pages, card_insert_of_notMem (parent_not_child hQ p)]
  omega

/--
@isnad1 id=le.1h5v.s7.f680242e46b2 from=translated src=- shape=c27c9903 vocab=10986e05
-/
theorem book_inter_parent_subset (_hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : support (pages P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases mem_pages.mp hT with rfl | ⟨_, hsub⟩
  · exact heT
  · exact hsub (mem_inter.mpr ⟨heT, heP⟩)

/--
@isnad1 id=disjoint.2h4v.s6.5ad0cdfe0581 from=translated src=- shape=b75ecfa6 vocab=7327907b
-/
theorem supports_disjoint (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.DisjointSupports (pages P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
  · have hep' := book_inter_parent_subset hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases mem_pages.mp hU with rfl | ⟨hUQ, hsubU⟩
    · have hep := book_inter_parent_subset hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · have hTU : T ≠ U := by
        intro hEq
        subst U
        exact hne (owner_unique hP.1 hQ hTQ p p' hsubT hsubU)
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

/--
@isnad1 id=ismaximu.3h5v.s7.1637e46dda11 from=translated src=- shape=d470873f vocab=94b66429
-/
theorem choices_maximum (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {f : {T // T ∈ P} → Finset (Sym2 V)} (hf : Books.ChoosesPages (pages P Q) f) :
    IsMaximumPacking (trianglesOn A) (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP.1 hQ)
    (supports_disjoint hP hQ)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family hP.1 hQ p hT)) ?_ hf
  intro K hK
  simpa using hP.2 K hK

/--
@isnad1 id=everycho.2h4v.s6.8ff3a4f23752 from=translated src=- shape=78c9eb22 vocab=98cdfc86
-/
theorem everyChoiceMeets (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.EveryChoiceMeets (trianglesOn A) (pages P Q) :=
  Books.everyChoiceMeets_of_maximum (fun _ hT => trianglesOn_nonempty hT)
    (fun _ hf => choices_maximum hP hQ hf)

/--
@isnad1 id=pairwise.2h4v.s7.bed9efee0dfa from=translated src=- shape=e820e433 vocab=e0bff47e
-/
theorem children_pairwise_disjoint (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Pairwise (fun p p' : {T // T ∈ P} =>
      Disjoint (children P Q p.val) (children P Q p'.val)) := by
  intro p p' hne
  apply disjoint_left.mpr
  intro q hq hq'
  obtain ⟨hqQ, hsub⟩ := mem_children.mp hq
  obtain ⟨_, hsub'⟩ := mem_children.mp hq'
  exact hne (owner_unique hP hQ hqQ p p' hsub hsub')

/--
@isnad1 id=eq.1h4v.s7.21974a9bde77 from=translated src=- shape=7e024977 vocab=9305d67d
-/
theorem children_biUnion (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    univ.biUnion (fun p : {T // T ∈ P} => children P Q p.val) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hq
    exact (mem_children.mp hp).1
  · intro hq
    exact mem_biUnion.mpr ⟨parent hQ ⟨q, hq⟩, mem_univ _,
      mem_children.mpr ⟨hq, parent_spec hQ ⟨q, hq⟩⟩⟩

/--
@isnad1 id=eq.2h4v.s7.2d23428788c1 from=translated src=- shape=8b333627 vocab=fab23833
-/
theorem sum_children_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (children P Q p.val).card) = Q.card := by
  conv_rhs => rw [← children_biUnion hQ]
  symm
  apply card_biUnion
  intro p _ p' _ hne
  exact children_pairwise_disjoint hP hQ hne

/--
@isnad1 id=eq.2h4v.s7.e7751e6807f3 from=translated src=- shape=ad052c19 vocab=1ce3cc3f
-/
theorem sum_pages_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (pages P Q p).card) = P.card + Q.card := by
  have hc : ∀ p : {T // T ∈ P}, (pages P Q p).card = (children P Q p.val).card + 1 := by
    intro p
    exact card_insert_of_notMem (parent_not_child hQ p)
  calc
    (∑ p : {T // T ∈ P}, (pages P Q p).card) =
        ∑ p : {T // T ∈ P}, ((children P Q p.val).card + 1) := sum_congr rfl (fun p _ => hc p)
    _ = P.card + Q.card := by rw [sum_add_distrib, sum_children_card hP hQ]; simp [Nat.add_comm]

/--
@isnad1 id=ex.2h5v.s7.cdba584de73e from=translated src=- shape=5d3d8c87 vocab=89b95046
-/
theorem pages_common_edge (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    ∃ e, ∀ T ∈ pages P Q p, e ∈ T := by
  by_cases hn : (children P Q p.val).Nonempty
  · obtain ⟨q, hq⟩ := hn
    obtain ⟨hqQ, hsubq⟩ := mem_children.mp hq
    obtain ⟨e, he⟩ := old_inter_nonempty hQ hqQ
    refine ⟨e, ?_⟩
    intro T hT
    rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
    · exact hsubq he
    · have hTchild := mem_children.mpr ⟨hTQ, hsubT⟩
      have hTq : T = q := card_le_one.mp (children_card_le_one hP hQ p) T hTchild q hq
      subst T
      exact (mem_inter.mp he).1
  · have hempty := not_nonempty_iff_eq_empty.mp hn
    obtain ⟨e, he⟩ := trianglesOn_nonempty (hP.1.1 p.property)
    refine ⟨e, ?_⟩
    intro T hT
    have ht : T = p.val := by simpa [pages, hempty] using hT
    subst T
    exact he

/-- The first cover saves one edge for every packed type-1 triangle.
@isnad1 id=ex.2h4v.s6.51fb00749514 from=translated src=- shape=d52a8808 vocab=317d6412
-/
theorem exists_first_cover (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    ∃ C : Finset (Sym2 V), IsCover (trianglesOn A) C ∧ C.card + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_cover_of_small_common_spine_books
    (trianglesOn A) (pages P Q) (pages_nonempty P Q)
    (fun p => (pages_card_le_two hP hQ p).trans (by decide))
    (fun p T hT => (mem_trianglesOn.mp (pages_subset_family hP.1 hQ p hT)).1)
    (pages_common_edge hP hQ) (fun T hT => (mem_trianglesOn.mp hT).1)
    (everyChoiceMeets hP hQ)
  rw [sum_pages_card hP.1 hQ] at hbound
  simp only [Fintype.card_coe] at hbound
  exact ⟨C, hC, by omega⟩

/--
@isnad1 id=le.2h4v.s6.d102ff6f2cb6 from=translated src=- shape=1877e2ab vocab=7a493619
-/
theorem transversalNumber_add_typeOne_packing_le (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    transversalNumber (trianglesOn A) + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_first_cover hP hQ
  have ht := hC.number_le
  omega

end FirstCover
end Tuza
